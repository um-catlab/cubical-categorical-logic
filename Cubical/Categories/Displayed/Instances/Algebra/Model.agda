-- Models of a Theory, displayed over their carrier set
module Cubical.Categories.Displayed.Instances.Algebra.Model where

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
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Presheaf.Representable

open import Cubical.Algebra.Theory.Base
  hiding (ℓ; ℓᴰ; ℓᴰᴰ; ℓ'; ℓᴰ'; ℓᴰᴰ'; ℓ''; ℓᴰ''; ℓO; ℓA; ℓE)

private
  variable
    ℓ : Level

open Category
open Categoryᴰ
open Functor
open UniversalElement
open UniversalElementᴰ
open isIsoOver

module _ {ℓO ℓA ℓE ℓEA} (T : Theory ℓO ℓA ℓE ℓEA) where
  open Theory T

  ModelLevel : Level
  ModelLevel = ℓ-max (ℓ-max ℓO ℓA) (ℓ-max ℓE ℓEA)

  MODELOver : ∀ ℓ →
    Categoryᴰ (SET ℓ)
      (ℓ-max ModelLevel ℓ)
      (ℓ-max (ℓ-max ℓO ℓA) ℓ)
  MODELOver ℓ .ob[_] = ModelStructure
  MODELOver ℓ .Hom[_][_,_] f A B =
    isHomoSimpl (_ , A .fst) (_ , B .fst) f
  MODELOver ℓ .idᴰ =
    λ op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ → op∘γ≡op⟨γ⟩
  MODELOver ℓ ._⋆ᴰ_ =
    λ z₁ z₂ op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ →
      z₂ op _ _ (z₁ op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)
  MODELOver ℓ .⋆IdLᴰ _ = refl
  MODELOver ℓ .⋆IdRᴰ _ = refl
  MODELOver ℓ .⋆Assocᴰ _ _ _ = refl
  MODELOver ℓ .isSetHomᴰ {y = Y} =
    isSetΠ3 λ _ _ _ → isSetΠ (λ _ → isProp→isSet (Y .snd _ _))

  MODEL : ∀ ℓ → Category _ _
  MODEL ℓ = ∫C (MODELOver ℓ)

  MODELForget : Functor (MODEL ℓ) (SET ℓ)
  MODELForget = TotalCat.Fst

  FreeMODEL : hSet ModelLevel → MODEL ModelLevel .ob
  FreeMODEL X = FreeModel ⟨ X ⟩

  MODELFree : LeftAdjoint (MODELForget {ℓ = ModelLevel})
  MODELFree X .UniversalElement.vertex = FreeMODEL X
  MODELFree X .UniversalElement.element = var
  MODELFree X .UniversalElement.universal B = isIsoToIsEquiv
    ( recFM ⟨ X ⟩ B
    , (λ _ → refl)
    , (λ ϕ → Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ → B .fst .snd _ _)
        (sym (recFM-uniq ⟨ X ⟩ B ϕ)))
    )

  module _ {ℓSET : Level} where
    TerminalMODELOver : Terminalᴰ (MODELOver ℓSET) TerminalSET
    TerminalMODELOver .vertexᴰ = ⊤*Model .snd
    TerminalMODELOver .elementᴰ = tt
    TerminalMODELOver .universalᴰ .inv _ _ _ _ _ _ = refl
    TerminalMODELOver .universalᴰ .rightInv _ _ = refl
    TerminalMODELOver .universalᴰ .leftInv _ _ =
      isProp→PathP
        (λ _ → isPropΠ4 λ _ _ _ _ → isSetUnit* _ _)
        _ _

    TerminalMODEL : Terminal' (MODEL ℓSET)
    TerminalMODEL =
      TerminalᴰNotation.∫term (MODELOver ℓSET) TerminalMODELOver

    BinProductsMODELOver : BinProductsᴰ (MODELOver ℓSET) BinProductsSET
    BinProductsMODELOver {c12 = X , Y} (A , B) .vertexᴰ =
      ((X , A) ×Model (Y , B)) .snd
    BinProductsMODELOver {c12 = X , Y} (A , B) .elementᴰ .fst
      op γ op⟨γ⟩ p = cong fst p
    BinProductsMODELOver {c12 = X , Y} (A , B) .elementᴰ .snd
      op γ op⟨γ⟩ p = cong snd p
    BinProductsMODELOver {c12 = X , Y} (A , B) .universalᴰ .inv
      _ (fᴰ , gᴰ) op γ op⟨γ⟩ p i =
        fᴰ op γ op⟨γ⟩ p i , gᴰ op γ op⟨γ⟩ p i
    BinProductsMODELOver {c12 = X , Y} (A , B) .universalᴰ .rightInv
      _ _ = refl
    BinProductsMODELOver {c12 = X , Y} (A , B) .universalᴰ .leftInv
      _ _ = refl

    BinProductsMODEL : BinProducts (MODEL ℓSET)
    BinProductsMODEL = BinProductsᴰNotation.∫bp BinProductsMODELOver
