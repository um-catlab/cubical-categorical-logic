{-

  Uncurried Presheaves using EqElement
-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS -W noUnsupportedIndexedMatch #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.HLevels
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions hiding (π₁Strict ; π₂Strict)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.StrictHom renaming (π₁ to π₁Strict ; π₂ to π₂Strict)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
import Cubical.Categories.Displayed.Instances.Sets.Base as Setᴰ
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq
import Cubical.Categories.Displayed.Presheaf.Base as Curried

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.Eq
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.Push
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.Fibration

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓE ℓE' ℓEᴰ ℓEᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open isIsoOver
open NatTrans
open NatTransᴰ
open NatIso
open NatIsoᴰ
open PshHomEq
open PshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  module _ {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
    (α : PshHomStrict P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) (Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ)
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    where
    *↑-⇒-commute :
      Iso (PshHomEq Pᴰ (α *↑ (Qᴰ ⇒PshLargeEq Rᴰ)))
          (PshHomEq Pᴰ ((α *↑ Qᴰ) ⇒PshLargeEq (α *↑ Rᴰ)))
    *↑-⇒-commute =
      PshHomEq Pᴰ (α *↑ (Qᴰ ⇒PshLargeEq Rᴰ))
        Iso⟨ invIso $ *↓-UMP α ⟩
      PshHomEq (α *↓ Pᴰ) (Qᴰ ⇒PshLargeEq Rᴰ)
        Iso⟨ ⇒PshLargeEq-UMP Qᴰ Rᴰ ⟩
      PshHomEq ((α *↓ Pᴰ) ×ⱽPsh Qᴰ) Rᴰ
        Iso⟨ precompPshIsoEq (FrobeniusReciprocity α Pᴰ Qᴰ) ⟩
      PshHomEq (α *↓ (Pᴰ ×ⱽPsh (α *↑ Qᴰ))) Rᴰ
        Iso⟨ *↓-UMP α ⟩
      PshHomEq (Pᴰ ×ⱽPsh (α *↑ Qᴰ)) (α *↑ Rᴰ)
        Iso⟨ invIso (⇒PshLargeEq-UMP (α *↑ Qᴰ) (α *↑ Rᴰ)) ⟩
      PshHomEq Pᴰ ((α *↑ Qᴰ) ⇒PshLargeEq (α *↑ Rᴰ))
      ∎Iso

  module _ {ℓP ℓPᴰ : Level}{P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    PSHᴰLRⱽ : LRⱽ (PRESHEAFᴰ Cᴰ ℓP ℓPᴰ) PSHReprEqAssoc Pᴰ
    PSHᴰLRⱽ = BPⱽ+Fibration→AllLRⱽ (PRESHEAFᴰ Cᴰ ℓP ℓPᴰ) PSHReprEqAssoc PSHᴰBPⱽ PSHᴰFibration Pᴰ

  module _ {ℓP ℓPᴰ} where
    private
       the-ℓ = ℓC ⊔ℓ ℓC' ⊔ℓ ℓP
       the-ℓᴰ = the-ℓ ⊔ℓ ℓCᴰ ⊔ℓ ℓCᴰ' ⊔ℓ ℓPᴰ
    PSHᴰExpsⱽ : Exponentialsⱽ (PRESHEAFᴰ Cᴰ the-ℓ the-ℓᴰ) PSHReprEqAssoc
                  (λ {x} {y} f → Eq.refl) PSHᴰLRⱽ
    PSHᴰExpsⱽ {x = P} Pᴰ Qᴰ .fst = Pᴰ ⇒PshLargeEq Qᴰ
    PSHᴰExpsⱽ {x = P} Pᴰ Qᴰ .snd .PshIsoEq.isos (R , Rᴰ , α) =
      PshHomEq Rᴰ (α *↑ (Pᴰ ⇒PshLargeEq Qᴰ))
        Iso⟨ invIso $ *↓-UMP α ⟩
      PshHomEq (α *↓ Rᴰ) (Pᴰ ⇒PshLargeEq Qᴰ)
        Iso⟨ ⇒PshLargeEq-UMP Pᴰ Qᴰ ⟩
      PshHomEq ((α *↓ Rᴰ) ×Psh Pᴰ) Qᴰ
        Iso⟨ precompPshIsoEq (FrobeniusReciprocity α Rᴰ Pᴰ) ⟩
      PshHomEq (α *↓ (Rᴰ ×Psh (α *↑ Pᴰ))) Qᴰ
        Iso⟨ *↓-UMP α ⟩
      PshHomEq (Rᴰ ×Psh (α *↑ Pᴰ)) (α *↑ Qᴰ)
      ∎Iso
    PSHᴰExpsⱽ {x = P} Pᴰ Qᴰ .snd .PshIsoEq.nat _ _ (_ , _ , Eq.refl) _ _ Eq.refl =
      Eq.pathToEq $ makePshHomEqPath (funExt₂ λ _ _ → refl)
