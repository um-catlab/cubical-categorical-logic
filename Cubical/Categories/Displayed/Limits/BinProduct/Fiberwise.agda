{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Limits.BinProduct.Fiberwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Fibration.Base
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

open import Cubical.Categories.Displayed.Limits.BinProduct.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open UniversalElement
open UniversalElementᴰ
open UniversalElementⱽ
open isIsoOver

module _ {C : Category ℓC ℓC'}(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  BinProductⱽ→BinProductFiber : ∀ {a} {aᴰ₁ aᴰ₂}
    → BinProductⱽ Cᴰ (aᴰ₁ , aᴰ₂)
    → BinProduct Cᴰ.v[ a ] (aᴰ₁ , aᴰ₂)
  BinProductⱽ→BinProductFiber bpⱽ = record
    { vertex = a₁×ⱽa₂.×ueⱽ.vertexⱽ
    ; element = a₁×ⱽa₂.×ueⱽ.elementⱽ
    ; universal = λ Γᴰ → isIsoToIsEquiv
      ( a₁×ⱽa₂.×ueⱽ.introⱽ
      , (λ f → a₁×ⱽa₂.×ueⱽ.Pshⱽ.rectify $ a₁×ⱽa₂.×ueⱽ.Pshⱽ.≡out $
        (sym $ a₁×ⱽa₂.×ueⱽ.Pshⱽ.reind-filler _ _)
        ∙ a₁×ⱽa₂.×ueⱽ.βᴰ
        )
      , λ f → Cᴰ.rectify $ Cᴰ.≡out $
        a₁×ⱽa₂.×ueⱽ.introᴰ≡ (sym $ a₁×ⱽa₂.×ueⱽ.Pshⱽ.reind-filler _ _)
        )
    } where
    module a₁×ⱽa₂ = BinProductⱽNotation _ bpⱽ
  BinProductsⱽ→BinProductsFibers :
    ∀ {a} → BinProductsⱽ Cᴰ → BinProducts Cᴰ.v[ a ]
  BinProductsⱽ→BinProductsFibers bpⱽ (aᴰ₁ , aᴰ₂) =
    BinProductⱽ→BinProductFiber (bpⱽ _ (aᴰ₁ , aᴰ₂))

  -- TODO: prove that cartesian lifts preserves these binary products
  cartesianLift-preserves-BinProductFiber :
    ∀ {a b aᴰ₁ aᴰ₂}
    → (isFib : isFibration Cᴰ)
    → (bpⱽ : BinProductⱽ Cᴰ (aᴰ₁ , aᴰ₂))
    → (f : C [ b , a ])
    → preservesBinProduct (CartesianLiftF-fiber Cᴰ isFib f)
      (BinProductⱽ→BinProductFiber bpⱽ)
  cartesianLift-preserves-BinProductFiber {b = b}{aᴰ₁}{aᴰ₂} isFib bpⱽ f bᴰ = isIsoToIsEquiv
    ( (λ (fⱽ₁ , fⱽ₂) → f*×.introCL (bpⱽ.×ueⱽ.introᴰ ((fⱽ₁ Cᴰ.⋆ᴰ f*aᴰ₁.π) , (fⱽ₂ Cᴰ.⋆ᴰ f*aᴰ₂.π))))
    , (λ (fⱽ₁ , fⱽ₂) → ΣPathP
        -- This part of the proof can probably be simplified
        ((Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ f*aᴰ₁.introCL-natural
          ∙ f*aᴰ₁.introCL≡' (C.⋆IdL _)
            ((sym $ Cᴰ.reind-filler _ _)
            ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆IdL _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩
            ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
            ∙ Cᴰ.⟨ f*×.βCL ⟩⋆⟨ refl ⟩
            ∙ Cᴰ.reind-filler _ _
            ∙ bpⱽ.∫×βⱽ₁))
        , (Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ f*aᴰ₂.introCL-natural
          ∙ f*aᴰ₂.introCL≡' (C.⋆IdL _)
            ((sym $ Cᴰ.reind-filler _ _)
            ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆IdL _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩
            ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
            ∙ Cᴰ.⟨ f*×.βCL ⟩⋆⟨ refl ⟩
            ∙ Cᴰ.reind-filler _ _
            ∙ bpⱽ.∫×βⱽ₂))
        ))
    , λ fⱽ → Cᴰ.rectify $ Cᴰ.≡out $
          f*×.introCL≡ (bpⱽ.,ⱽ≡
            (Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
              ∙ Cᴰ.⋆Assoc _ _ _
              ∙ Cᴰ.⟨ refl ⟩⋆⟨ f*aᴰ₁.βCL ∙ Cᴰ.⋆IdL _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩
              ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
              ∙ Cᴰ.reind-filler _ _)
            (Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
              ∙ Cᴰ.⋆Assoc _ _ _
              ∙ Cᴰ.⟨ refl ⟩⋆⟨ f*aᴰ₂.βCL ∙ Cᴰ.⋆IdL _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩
              ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
              ∙ Cᴰ.reind-filler _ _))
      )
    where
    module f*× = CartesianLift (isFib (vertexⱽ bpⱽ) f)
    module f*aᴰ₁ = CartesianLift (isFib aᴰ₁ f)
    module f*aᴰ₂ = CartesianLift (isFib aᴰ₂ f)
    module bpⱽ = BinProductⱽNotation _ bpⱽ
    module f*⟨aᴰ₁×aᴰ₂⟩ = PresheafNotation (BinProductProf Cᴰ.v[ b ] ⟅ f*aᴰ₁.f*yᴰ , f*aᴰ₂.f*yᴰ ⟆)

  BinProductsWithⱽ→BinProductsWithFiber : ∀ {a} {aᴰ}
    → BinProductsWithⱽ Cᴰ aᴰ
    → BinProductsWith Cᴰ.v[ a ] aᴰ
  BinProductsWithⱽ→BinProductsWithFiber -×ⱽaᴰ aᴰ' =
    BinProductⱽ→BinProductFiber (-×ⱽaᴰ aᴰ')
