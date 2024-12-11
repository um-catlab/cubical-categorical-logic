{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Presheaf.CartesianLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
import Cubical.Categories.Displayed.Fibration.Base as Fibration

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓQ ℓPᴰ ℓQᴰ : Level

open Category
open Functor
open Functorᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP}
         where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  record CartesianLift {x : C .ob} (p : ⟨ P ⟅ x ⟆ ⟩) (Pᴰ : Presheafᴰ Cᴰ P ℓPᴰ) : Type
    (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') ℓPᴰ)) where
    field
      p*Pᴰ : Cᴰ.ob[ x ]
      π : ⟨ Pᴰ .F-obᴰ p*Pᴰ p ⟩
      isCartesian : ∀ {z zᴰ}{g : C [ z , x ]} →
        isIso (λ (gᴰ : Cᴰ [ g ][ zᴰ , p*Pᴰ ]) → Pᴰ .F-homᴰ gᴰ p π)

open CartesianLift
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ Cᴰ P ℓPᴰ)
         where
  hasAllCartesianLifts = ∀ {x} (p : ⟨ P ⟅ x ⟆ ⟩) → CartesianLift p Pᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  -- TODO: should we just define Fibration.CartesianLift this way?
  fibLift→PshᴰLift : ∀ {x y yᴰ}{f : C [ x , y ]}
    → Fibration.CartesianLift Cᴰ yᴰ f
    → CartesianLift f (Cᴰ [-][-, yᴰ ])
  fibLift→PshᴰLift = λ z →
                        record
                        { p*Pᴰ = z .Fibration.CartesianLift.f*yᴰ
                        ; π = z .Fibration.CartesianLift.π
                        ; isCartesian = z .Fibration.CartesianLift.isCartesian
                        }

  PshᴰLift→fibLift : ∀ {x y yᴰ}{f : C [ x , y ]}
    → CartesianLift f (Cᴰ [-][-, yᴰ ])
    → Fibration.CartesianLift Cᴰ yᴰ f
  PshᴰLift→fibLift = λ z →
                        record
                        { f*yᴰ = z .CartesianLift.p*Pᴰ
                        ; π = z .CartesianLift.π
                        ; isCartesian = z .CartesianLift.isCartesian
                        }

  isFibration→hasAllCartesianLifts :
    Fibration.isFibration Cᴰ
    → ∀ {y} (yᴰ : Cᴰ.ob[ y ]) → hasAllCartesianLifts (Cᴰ [-][-, yᴰ ])
  isFibration→hasAllCartesianLifts isFib yᴰ p .CartesianLift.p*Pᴰ = isFib yᴰ p .Fibration.CartesianLift.f*yᴰ
  isFibration→hasAllCartesianLifts isFib yᴰ p .CartesianLift.π = isFib yᴰ p .Fibration.CartesianLift.π
  isFibration→hasAllCartesianLifts isFib yᴰ p .CartesianLift.isCartesian = isFib yᴰ p .Fibration.CartesianLift.isCartesian

-- say I have Dᴰ ⊏ D and a presheaf Qᴰ ⊏ Q with and a psh P on D with α : P ⇒ Q
-- then can we show that α* Qᴰ ⊏ P has all cartesian lifts? (sounds new)
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
         (Qᴰ : Presheafᴰ Cᴰ Q ℓQᴰ) (α : PshHomⱽ P Q)
         where
  private
    module Qᴰ = PresheafᴰReasoning Qᴰ
  hasAllCartesianLiftsPshReind
    : hasAllCartesianLifts Qᴰ
    → hasAllCartesianLifts (PshReind {P = P} Qᴰ α) -- isFibQᴰ (α .fst _ p)
  hasAllCartesianLiftsPshReind isFibQᴰ p .p*Pᴰ = isFibQᴰ (α .fst _ p) .p*Pᴰ
  hasAllCartesianLiftsPshReind isFibQᴰ p .π = isFibQᴰ (α .fst _ p) .π
  hasAllCartesianLiftsPshReind isFibQᴰ p .isCartesian .fst qᴰ =
    isFibQᴰ (α .fst _ p) .isCartesian .fst (Qᴰ.reind (α .snd _ p) qᴰ)
  hasAllCartesianLiftsPshReind isFibQᴰ p .isCartesian .snd .fst qᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $
      (sym $ Qᴰ.reind-filler _ _)
      ∙ (Qᴰ.≡in $ isFibQᴰ (α .fst _ p) .isCartesian .snd .fst _)
      ∙ (sym $ Qᴰ.reind-filler _ _)
  hasAllCartesianLiftsPshReind isFibQᴰ p .isCartesian .snd .snd gᴰ =
    cong (isFibQᴰ (α .fst _ p) .isCartesian .fst)
      (Qᴰ.rectify $ Qᴰ.≡out $
      (sym $ Qᴰ.reind-filler _ _) ∙ (sym $ Qᴰ.reind-filler _ _))
    ∙ isFibQᴰ (α .fst _ p) .isCartesian .snd .snd _

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (F : Functor C D)
         where
  module _ {P : Presheaf D ℓP} (Pᴰ : Presheafᴰ Dᴰ P ℓPᴰ) where
    -- incredible!!!
    reindexFunctorCartLifts
      : hasAllCartesianLifts Pᴰ
      → hasAllCartesianLifts (Pᴰ ∘Fᴰ (Reindex.π Dᴰ F ^opFᴰ))
    reindexFunctorCartLifts isFib pF .p*Pᴰ = isFib pF .p*Pᴰ
    reindexFunctorCartLifts isFib pF .π = isFib pF .π
    reindexFunctorCartLifts isFib pF .isCartesian = isFib pF .isCartesian

  -- can we use this to prove isFibrationReindex?
  -- !!!
  -- TODO: only make the relevant part (isCartesian) opaque
  opaque
    unfolding PresheafᴰReasoning.reind
    isFibrationReindex : Fibration.isFibration Dᴰ
      → Fibration.isFibration (Reindex.reindex Dᴰ F)
    isFibrationReindex isFib {c' = c'} cᴰ' f =
      let bar = hasAllCartesianLiftsPshReind {P = C [-, c' ]} ((Dᴰ [-][-, cᴰ' ]) ∘Fᴰ (Reindex.π Dᴰ F ^opFᴰ)) ((λ x → F .F-hom) , λ {x} {y} → F .F-seq) (reindexFunctorCartLifts (Dᴰ [-][-, cᴰ' ]) ((λ p → fibLift→PshᴰLift (isFib cᴰ' p)))) f in
      PshᴰLift→fibLift $ record
      { p*Pᴰ = bar .p*Pᴰ
      ; π = bar .π
      ; isCartesian = bar .isCartesian
      }
