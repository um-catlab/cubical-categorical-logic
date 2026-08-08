-- Algebras of a Signature, displayed over their carrier set
module Cubical.Categories.Displayed.Instances.Algebra.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.BinProduct as BP
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Instances.TotalCategory as TotalCat
open import Cubical.Categories.Limits.BinProduct.More using (BinProducts)
open import Cubical.Categories.Limits.Terminal.More using (Terminal')
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Profunctor.Relator

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Presheaf.Representable

open import Cubical.Algebra.Signature.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level

open Category
open Categoryᴰ
open StructureOver
open Functor
open UniversalElement
open UniversalElementᴰ
open isIsoOver

module _ {ℓO ℓA}(Sig : Signature ℓO ℓA) where
  open Signature Sig
  ALGOver : ∀ ℓ → Categoryᴰ (SET ℓ) (ℓ-max (ℓ-max ℓO ℓA) ℓ) (ℓ-max (ℓ-max ℓO ℓA) ℓ)
  ALGOver ℓ .ob[_] X = AlgebraWithCarrier ⟨ X ⟩
  ALGOver ℓ .Hom[_][_,_] f A B = isHomoSimpl (_ , A)(_ , B) f
  ALGOver ℓ .idᴰ = λ op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ → op∘γ≡op⟨γ⟩
  ALGOver ℓ ._⋆ᴰ_ = λ z₁ z₂ op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ →
                       z₂ op _ _ (z₁ op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)
  ALGOver ℓ .⋆IdLᴰ _ = refl
  ALGOver ℓ .⋆IdRᴰ _ = refl
  ALGOver ℓ .⋆Assocᴰ _ _ _ = refl
  ALGOver ℓ .isSetHomᴰ {y = Y}= isSetΠ3 λ _ _ _ → isSetΠ (λ _ → isProp→isSet (Y .snd _ _))

  ALG : ∀ ℓ → Category _ _
  ALG ℓ = ∫C (ALGOver ℓ)

  AlgebraLevel : Level
  AlgebraLevel = ℓ-max ℓO ℓA

  module _ (isSetOp : isSet Op) where
    ALGForget : Functor (ALG AlgebraLevel) (SET AlgebraLevel)
    ALGForget = TotalCat.Fst

    FreeALG : hSet AlgebraLevel → ALG AlgebraLevel .ob
    FreeALG X .fst = |FreeAlgebra| ⟨ X ⟩ , isSetFreeAlgebra isSetOp (X .snd)
    FreeALG X .snd = app

    ALGFree : LeftAdjoint ALGForget
    ALGFree X .UniversalElement.vertex = FreeALG X
    ALGFree X .UniversalElement.element = var
    ALGFree X .UniversalElement.universal B = isIsoToIsEquiv
      ( (recFA (_ , B .snd))
      , (λ _ → refl)
      , (λ ϕ → Σ≡Prop
          (λ _ → isPropΠ4 λ _ _ _ _ → B .fst .snd _ _)
          (sym (recFA-uniq (_ , B .snd) ϕ)))
      )

  module _ {ℓSET : Level} where
    TerminalALGOver : Terminalᴰ (ALGOver ℓSET) TerminalSET
    TerminalALGOver .vertexᴰ = ⊤*Algebra
    TerminalALGOver .elementᴰ = tt
    TerminalALGOver .universalᴰ .inv _ _ _ _ _ _ = refl
    TerminalALGOver .universalᴰ .rightInv _ _ = refl
    TerminalALGOver .universalᴰ .leftInv _ _ =
      isProp→PathP
        (λ _ → isPropΠ4 λ _ _ _ _ → isSetUnit* _ _)
        _ _

    BinProductsALGOver : BinProductsᴰ (ALGOver ℓSET) BinProductsSET
    BinProductsALGOver {c12 = X , Y} (A , B) .vertexᴰ = ((_ , A) ×Alg (_ , B)) .snd
    BinProductsALGOver {c12 = X , Y} (A , B) .elementᴰ .fst op γ op⟨γ⟩ p = cong fst p
    BinProductsALGOver {c12 = X , Y} (A , B) .elementᴰ .snd op γ op⟨γ⟩ p = cong snd p
    BinProductsALGOver {c12 = X , Y} (A , B) .universalᴰ .inv _ (fᴰ , gᴰ) op γ op⟨γ⟩ p i =
        fᴰ op γ op⟨γ⟩ p i , gᴰ op γ op⟨γ⟩ p i
    BinProductsALGOver {c12 = X , Y} (A , B) .universalᴰ .rightInv _ _ = refl
    BinProductsALGOver {c12 = X , Y} (A , B) .universalᴰ .leftInv _ _ = refl

    TerminalALG : Terminal' (ALG ℓSET)
    TerminalALG = TerminalᴰNotation.∫term (ALGOver ℓSET) TerminalALGOver

    BinProductsALG : BinProducts (ALG ℓSET)
    BinProductsALG = BinProductsᴰNotation.∫bp BinProductsALGOver

  -- TODO: ALGOver is an IsoFibration
