{-

  Uncurried Presheaves using EqElement
-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS -W noUnsupportedIndexedMatch #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.Quantifiers where

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

-- TODO put this somewhere central to avoid duplication for Uncurried.Eq.Presheaves.Base
module _ {C : Category ℓC ℓC'} where
  PSHIdR : EqIdR (PRESHEAF C ℓP)
  PSHIdR = λ f → Eq.refl

  PSHIdL : EqIdL (PRESHEAF C ℓP)
  PSHIdL = λ f → Eq.refl

  PSHAssoc : ReprEqAssoc (PRESHEAF C ℓP)
  PSHAssoc _ f g h f⋆g Eq.refl = Eq.refl

  PSHBP : BinProducts (PRESHEAF C ℓP)
  PSHBP (P , Q) .UniversalElement.vertex = P ×Psh Q
  PSHBP (P , Q) .UniversalElement.element = π₁Strict P Q , π₂Strict P Q
  PSHBP (P , Q) .UniversalElement.universal R = isIsoToIsEquiv
    ( (λ x → ×PshIntroStrict (x .fst) (x .snd)) , ((λ _ → refl) , (λ _ → refl)))

  PSHπ₁NatEq : Allπ₁NatEq {C = PRESHEAF C ℓP} PSHBP
  PSHπ₁NatEq X γ = Eq.refl

  PSH×aF-seq : All×aF-seq {C = PRESHEAF C ℓP} PSHBP
  PSH×aF-seq X δ γ = Eq.refl
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {ℓP ℓPᴰ : Level} where
  PSHᴰ∀ : UniversalQuantifiers (PRESHEAFᴰ Cᴰ {!!} {!!})
    PSHIdR PSHReprEqAssoc PSHᴰFibration PSHBP PSHπ₁NatEq PSH×aF-seq
  PSHᴰ∀ P Pᴰ .fst = {!Pshᴰ!}
  PSHᴰ∀ P Pᴰ .snd = {!!}

  -- -- Pᴰ : Pshᴰ (P × Q)
  -- -- -----------------
  -- -- (∀Q Pᴰ) (Γ , Γᴰ , p) = PshHom ? Pᴰ
  -- PSHᴰ∀ Q {P} Pᴰ .fst = ∀Pshᴰ Pᴰ

  -- PSHᴰ∀ Q {P} Pᴰ .snd .PshIsoEq.isos (R , Rᴰ , α) =
  --   PshHom Rᴰ (α *Strict ∀Pshᴰ Pᴰ)
  --     Iso⟨ Push⊣* (PshHomStrict→Eq α) Rᴰ (∀Pshᴰ Pᴰ) ⟩
  --   PshHom (α PushStrict Rᴰ) (∀Pshᴰ Pᴰ)
  --     Iso⟨ invIso {!!} ⟩
  --   PshHom (π₁ P Q *Strict α PushStrict Rᴰ) Pᴰ
  --     -- Beck Chevalley
  --     Iso⟨ precomp⋆PshHom-Iso (BeckChevalley α Rᴰ) ⟩
  --   PshHom (×PshIntroStrict (π₁ R Q ⋆PshHomStrict α) (π₂ R Q) PushStrict (π₁ R Q) *Strict Rᴰ) Pᴰ
  --     Iso⟨ invIso $ Push⊣* _ _ _ ⟩
  --   PshHom (π₁ R Q *Strict Rᴰ) (×PshIntroStrict (π₁ R Q ⋆PshHomStrict α) (π₂ R Q) *Strict Pᴰ)
  --     ∎Iso
  -- PSHᴰ∀ Q {P} Pᴰ .snd .PshIsoEq.nat = {!!}

  -- isCartesianClosedⱽPSHᴰ : isCartesianClosedⱽ PSHAssoc (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHIdL  PSHBP PSHπ₁NatEq PSH×aF-seq
  -- isCartesianClosedⱽPSHᴰ .fst = isCartesianⱽPSHᴰ
  -- isCartesianClosedⱽPSHᴰ .snd .fst = PSHᴰExponentials
  -- isCartesianClosedⱽPSHᴰ .snd .snd = PSHᴰ∀
