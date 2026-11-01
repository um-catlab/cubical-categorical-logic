-- Models of a Theory, displayed over their carrier set
module Cubical.Categories.Displayed.Instances.Algebra.Model where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_$_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Instances.TotalCategory as TotalCat
open import Cubical.Categories.Limits.BinProduct.More using (BinProducts)
open import Cubical.Categories.Limits.Terminal.More using (Terminal')
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Presheaf.Representable

open import Cubical.Algebra.Theory.Base

private
  variable
    ℓ : Level

open Category
open Categoryᴰ
open Functor
open UniversalElement
open UniversalElementᴰ
open isIsoOver
open isIso

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

  isFaithfulMODELForget : isFaithful (MODELForget {ℓ = ℓ})
  isFaithfulMODELForget X Y ϕ ψ =
    Σ≡Prop (λ _ → isPropΠ4 λ _ _ _ _ → Y .fst .snd _ _)

  MODELFree : LeftAdjoint (MODELForget {ℓ = ModelLevel})
  MODELFree X .UniversalElement.vertex = FreeModel ⟨ X ⟩
  MODELFree X .UniversalElement.element = var
  MODELFree X .UniversalElement.universal B = isIsoToIsEquiv
    ( recFM ⟨ X ⟩ B
    , (λ _ → refl)
    , (λ ϕ → isFaithfulMODELForget (FreeModel ⟨ X ⟩) B _ ϕ
        (sym (recFM-uniq ⟨ X ⟩ B ϕ))))

  FreeMODELIso : {X Y : hSet ModelLevel} → Iso ⟨ X ⟩ ⟨ Y ⟩
    → CatIso (MODEL ModelLevel) (FreeModel ⟨ X ⟩) (FreeModel ⟨ Y ⟩)
  FreeMODELIso {X} {Y} e =
    preserveIsosF {F = LeftAdjoint→Functor MODELForget MODELFree}
      (Iso→CatIso {A = X} {B = Y} e)

  module _ {X : hSet ModelLevel} (M : MODEL ModelLevel .ob)
    (η : ⟨ X ⟩ → ⟨ M .fst ⟩)
    (univ : (B : MODEL ModelLevel .ob)
      → isEquiv (λ (ϕ : MODEL ModelLevel [ M , B ]) x → ϕ .fst (η x)))
    where
    private
      ue : LeftAdjointAt MODELForget X
      ue .vertex = M
      ue .element = η
      ue .universal = univ

      module U = UniversalElementNotation ue
      module F = UniversalElementNotation (MODELFree X)

    FreeMODEL≅ : CatIso (MODEL ModelLevel) (FreeModel ⟨ X ⟩) M
    FreeMODEL≅ .fst = F.intro {c = M} η
    FreeMODEL≅ .snd .inv = U.intro {c = FreeModel ⟨ X ⟩} F.element
    FreeMODEL≅ .snd .sec = U.extensionality {c = M}
      (funExt λ x → cong (F.intro {c = M} η .fst)
        (funExt⁻ (U.β {c = FreeModel ⟨ X ⟩} {p = F.element}) x))
    FreeMODEL≅ .snd .ret = F.extensionality {c = FreeModel ⟨ X ⟩}
      (funExt λ x → funExt⁻ (U.β {c = FreeModel ⟨ X ⟩} {p = F.element}) x)

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
