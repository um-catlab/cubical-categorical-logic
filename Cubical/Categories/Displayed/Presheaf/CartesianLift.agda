{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.CartesianLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor
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
    module Cᴰ = Fibers Cᴰ
  record CartesianLift {x : C .ob} (p : ⟨ P ⟅ x ⟆ ⟩) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) : Type
    (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') ℓPᴰ)) where
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ
    field
      p*Pᴰ : Cᴰ.ob[ x ]
      π : Pᴰ.p[ p ][ p*Pᴰ ]
      isCartesian : ∀ {z zᴰ}{g : C [ z , x ]} →
        isIso (λ (gᴰ : Cᴰ [ g ][ zᴰ , p*Pᴰ ]) → gᴰ Pᴰ.⋆ᴰ π)


    -- TODO: port all of the methods from Fibration.Base to here.
    opaque
      intro :
        ∀ {z zᴰ}{g : C [ z , x ]}
        → Pᴰ.p[ g P.⋆ p ][ zᴰ ]
        → Cᴰ [ g ][ zᴰ , p*Pᴰ ]
      intro = isCartesian .fst
    opaque
      unfolding intro
      private
        intro⟨_⟩ :
          ∀ {z zᴰ}{g g' : C [ z , x ]}
          → {gpᴰ : Pᴰ.p[ g P.⋆ p ][ zᴰ ]}
          → {gpᴰ' : Pᴰ.p[ g' P.⋆ p ][ zᴰ ]}
          → (g , gpᴰ) ≡ (g' , gpᴰ')
          → (g , intro gpᴰ) ≡ (g' , intro gpᴰ')
        intro⟨ gp≡gp' ⟩ i .fst = gp≡gp' i .fst
        intro⟨ gp≡gp' ⟩ i .snd = intro $ gp≡gp' i .snd

      intro⟨_⟩⟨_⟩ :
        ∀ {z zᴰ}{g g' : C [ z , x ]}
        → {gpᴰ : Pᴰ.p[ g P.⋆ p ][ zᴰ ]}
        → {gpᴰ' : Pᴰ.p[ g' P.⋆ p ][ zᴰ ]}
        → g ≡ g'
        → Path Pᴰ.p[ _ ] (_ , gpᴰ) (_ , gpᴰ')
        → Path Cᴰ.Hom[ _ , _ ] (_ , intro gpᴰ) (_ , intro gpᴰ')
      intro⟨ g≡g' ⟩⟨ gpᴰ≡gpᴰ' ⟩ =
        intro⟨ ΣPathP (g≡g' , (Pᴰ.rectify $ Pᴰ.≡out $ gpᴰ≡gpᴰ')) ⟩

      β :
        ∀ {z zᴰ}{g : C [ z , x ]}
        → {gpᴰ : Pᴰ.p[ g P.⋆ p ][ zᴰ ]}
        → Path Pᴰ.p[ _ ]
            (_ , (intro gpᴰ Pᴰ.⋆ᴰ π))
            (_ , gpᴰ)
      β = Pᴰ.≡in $ isCartesian .snd .fst _

      intro≡ :
        ∀ {z zᴰ}{g : C [ z , x ]}
        → {gpᴰ : Pᴰ.p[ g P.⋆ p ][ zᴰ ]}
        → {gᴰ : Cᴰ [ g ][ zᴰ , p*Pᴰ ]}
        → Path Pᴰ.p[ _ ]
            (_ , gpᴰ)
            (_ , (gᴰ Pᴰ.⋆ᴰ π))
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , intro gpᴰ)
            (_ , gᴰ)
      intro≡ gp≡gπ =
        intro⟨ refl ⟩⟨ gp≡gπ ⟩
        ∙ (Cᴰ.≡in (isCartesian .snd .snd _))


open CartesianLift
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
         where
  private
    module P = PresheafNotation P
  isFibration = ∀ {x} (p : P.p[ x ]) → CartesianLift p Pᴰ

  module isFibrationNotation (isFibPᴰ : isFibration) where
    module _ {x} (p : P.p[ x ]) where
      open CartesianLift (isFibPᴰ p) using (p*Pᴰ) public
    module _ {x} {p : P.p[ x ]} where
      open CartesianLift (isFibPᴰ p) hiding (p*Pᴰ) public

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         where
  private
    module Cᴰ = Categoryᴰ Cᴰ

  -- TODO: This definitional isomorphism seems to justify defining
  -- Fibration.CartesianLift as YoLift
  CatLift→YoLift : ∀ {x y yᴰ}{f : C [ x , y ]}
    → Fibration.CartesianLift Cᴰ yᴰ f
    → CartesianLift f (Cᴰ [-][-, yᴰ ])
  CatLift→YoLift = λ z →
                        record
                        { p*Pᴰ = z .Fibration.CartesianLift.f*yᴰ
                        ; π = z .Fibration.CartesianLift.π
                        ; isCartesian = z .Fibration.CartesianLift.isCartesian
                        }

  YoLift→CatLift : ∀ {x y yᴰ}{f : C [ x , y ]}
    → CartesianLift f (Cᴰ [-][-, yᴰ ])
    → Fibration.CartesianLift Cᴰ yᴰ f
  YoLift→CatLift = λ z →
                        record
                        { f*yᴰ = z .CartesianLift.p*Pᴰ
                        ; π = z .CartesianLift.π
                        ; isCartesian = z .CartesianLift.isCartesian
                        }

  YoFibrations : Type _
  YoFibrations = ∀ {y} (yᴰ : Cᴰ.ob[ y ]) → isFibration (Cᴰ [-][-, yᴰ ])

  isCatFibration→YoFibrations : Fibration.isFibration Cᴰ → YoFibrations
  isCatFibration→YoFibrations isFib yᴰ p = CatLift→YoLift $ isFib yᴰ p

  YoFibrations→isCatFibration : YoFibrations → Fibration.isFibration Cᴰ
  YoFibrations→isCatFibration YoLifts cᴰ' f = YoLift→CatLift $ YoLifts cᴰ' f

-- say I have Dᴰ ⊏ D and a presheaf Qᴰ ⊏ Q with and a psh P on D with α : P ⇒ Q
-- then can we show that α* Qᴰ ⊏ P has all cartesian lifts? (sounds new)
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
         (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) (α : PshHom P Q)
         (isFibQᴰ : isFibration Qᴰ)
         where
  private
    module Cᴰ = Fibers Cᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    module isFibQᴰ = isFibrationNotation Qᴰ isFibQᴰ
  isFibrationReind : isFibration (reind {P = P} α Qᴰ)
  isFibrationReind p .p*Pᴰ = isFibQᴰ.p*Pᴰ (α .fst _ p)
  isFibrationReind p .π = isFibQᴰ.π
  isFibrationReind p .isCartesian .fst qᴰ =
    isFibQᴰ.intro $ Qᴰ.reind (α .snd _ _ _ p) qᴰ
  isFibrationReind p .isCartesian .snd .fst qᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $
      sym (Qᴰ.reind-filler _ _)
      ∙ isFibQᴰ.β
      ∙ (sym $ Qᴰ.reind-filler _ _)
  isFibrationReind p .isCartesian .snd .snd gᴰ =
    Cᴰ.rectify $ Cᴰ.≡out $ isFibQᴰ.intro≡ $ sym $
      Qᴰ.reind-filler _ _ ∙ Qᴰ.reind-filler _ _

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (F : Functor C D)
         where
  module _ {P : Presheaf D ℓP} (Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ) (isFibPᴰ : isFibration Pᴰ) where
    -- incredible!!!
    reindexFunctorCartLifts
      : isFibration (Pᴰ ∘Fᴰ (Reindex.π Dᴰ F ^opFᴰ))
    reindexFunctorCartLifts p .p*Pᴰ = p*Pᴰ (isFibPᴰ p)
    reindexFunctorCartLifts p .π = π (isFibPᴰ p)
    reindexFunctorCartLifts p .isCartesian = isCartesian (isFibPᴰ p)

  -- This gives us a very interesting alternate proof of isFibrationReindex
  module _ (isFibDᴰ : Fibration.isFibration Dᴰ) where
    open Fibration.CartesianLift
    private
      module Dᴰ = Categoryᴰ Dᴰ

    isCatFibrationReindex : Fibration.isFibration (Reindex.reindex Dᴰ F)
    isCatFibrationReindex = YoFibrations→isCatFibration yF where
      module _ {y} (yᴰ  : Dᴰ.ob[ F ⟅ y ⟆ ]) where
        isFiblem : isFibration _
        isFiblem = isFibrationReind _
          (functor→YoPshHom F y)
          (reindexFunctorCartLifts (Dᴰ [-][-, yᴰ ]) (isCatFibration→YoFibrations isFibDᴰ yᴰ))
      yF : YoFibrations
      yF yᴰ p .p*Pᴰ = isFiblem yᴰ p .p*Pᴰ
      yF yᴰ p .π = isFibDᴰ yᴰ (F ⟪ p ⟫) .π
      yF yᴰ p .isCartesian = isFiblem yᴰ p .isCartesian
