{-# OPTIONS --safe --lossy-unification #-}
{- This file takes a *very* long time to type check -}
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
    → BinProduct'' Cᴰ.v[ a ] (aᴰ₁ , aᴰ₂)
  BinProductⱽ→BinProductFiber bpⱽ = record
    { vertex = a₁×ⱽa₂.vertexⱽ
    ; element = a₁×ⱽa₂.elementⱽ
    ; universal = λ Γᴰ → isIsoToIsEquiv
      ( a₁×ⱽa₂.introⱽ
      , (λ f → a₁×ⱽa₂.Pshⱽ.rectify $ a₁×ⱽa₂.Pshⱽ.≡out $
        (sym $ a₁×ⱽa₂.Pshⱽ.reind-filler _ _)
        ∙ (a₁×ⱽa₂.Pshⱽ.≡in $ a₁×ⱽa₂.βᴰ))
      , λ f → Cᴰ.rectify $ Cᴰ.≡out $
        a₁×ⱽa₂.introᴰ⟨ sym $ a₁×ⱽa₂.Pshⱽ.reind-filler _ _ ⟩
        ∙ (sym $ Cᴰ.≡in $ a₁×ⱽa₂.ηᴰ))
    } where
    module a₁×ⱽa₂ = UniversalElementⱽNotation _ _ _ bpⱽ
  hasAllBinProductⱽ→BinProductFibers :
    ∀ {a} → hasAllBinProductⱽ Cᴰ → BinProducts'' Cᴰ.v[ a ]
  hasAllBinProductⱽ→BinProductFibers bpⱽ (aᴰ₁ , aᴰ₂) =
    BinProductⱽ→BinProductFiber (bpⱽ (aᴰ₁ , aᴰ₂))

  -- TODO: prove that cartesian lifts preserves these binary products
  cartesianLift-preserves-BinProductFiber :
    ∀ {a b aᴰ₁ aᴰ₂}
    → (isFib : isFibration Cᴰ)
    → (bpⱽ : BinProductⱽ Cᴰ (aᴰ₁ , aᴰ₂))
    → (f : C [ b , a ])
    → preservesBinProduct' (CartesianLiftF-fiber Cᴰ isFib f)
      (BinProductⱽ→BinProductFiber bpⱽ)
  cartesianLift-preserves-BinProductFiber {b = b}{aᴰ₁}{aᴰ₂} isFib bpⱽ f bᴰ = isIsoToIsEquiv
    ( (λ (fⱽ₁ , fⱽ₂) → f*×.introCL (bpⱽ.introᴰ _ ((fⱽ₁ Cᴰ.⋆ᴰ f*aᴰ₁.π) , (fⱽ₂ Cᴰ.⋆ᴰ f*aᴰ₂.π))))
    , (λ (fⱽ₁ , fⱽ₂) → ΣPathP
        -- This part of the proof can probably be simplified
        ( (Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ (Cᴰ.≡in $ f*aᴰ₁.introCL-natural)
          ∙ f*aᴰ₁.introCL⟨ refl ⟩⟨
            (sym $ Cᴰ.reind-filler _ _)
            ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.≡in (Cᴰ.⋆IdLᴰ _) ∙ (sym $ Cᴰ.reind-filler _ _) ⟩
            ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
            ∙ Cᴰ.⟨ f*×.βCL ⟩⋆⟨ refl ⟩
            ∙ Cᴰ.reind-filler _ _
            ∙ (Cᴰ.≡in $ bpⱽ'.×βⱽ₁)
            ∙ Cᴰ.reind-filler C.⟨ sym (C.⋆IdL _) ⟩⋆⟨ refl ⟩ _
            ⟩
          ∙ f*aᴰ₁.introCL⟨ C.⋆IdL _ ⟩⟨ sym $ Cᴰ.reind-filler _ _ ⟩
          ∙ (sym $ f*aᴰ₁.ηCL)
          )
        , ((Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ (Cᴰ.≡in $ f*aᴰ₂.introCL-natural)
          ∙ f*aᴰ₂.introCL⟨ refl ⟩⟨
            (sym $ Cᴰ.reind-filler _ _)
            ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.≡in (Cᴰ.⋆IdLᴰ _) ∙ (sym $ Cᴰ.reind-filler _ _) ⟩
            ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
            ∙ Cᴰ.⟨ f*×.βCL ⟩⋆⟨ refl ⟩
            ∙ Cᴰ.reind-filler _ _
            ∙ (Cᴰ.≡in $ bpⱽ'.×βⱽ₂)
            ∙ Cᴰ.reind-filler C.⟨ sym (C.⋆IdL _) ⟩⋆⟨ refl ⟩ _
            ⟩
          ∙ f*aᴰ₂.introCL⟨ C.⋆IdL _ ⟩⟨ sym $ Cᴰ.reind-filler _ _ ⟩
          ∙ (sym $ f*aᴰ₂.ηCL)) )
        ))
    , λ fⱽ → Cᴰ.rectify $ Cᴰ.≡out $
          f*×.introCL⟨ refl ⟩⟨
            bpⱽ.∫ue.intro≡ (ΣPathP $
              (sym $ C.⋆IdR _)
              , ΣPathP
                ( (Cᴰ.rectify $ Cᴰ.≡out $
                  Cᴰ.⟨ (sym $ Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
                  ∙ Cᴰ.⋆Assoc _ _ _
                  ∙ Cᴰ.⟨ refl ⟩⋆⟨ f*aᴰ₁.βCL ⟩
                  ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆IdL _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩
                  ∙ (sym $ Cᴰ.⋆Assoc _ _ _))
                , (Cᴰ.rectify $ Cᴰ.≡out $
                  Cᴰ.⟨ (sym $ Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
                  ∙ Cᴰ.⋆Assoc _ _ _
                  ∙ Cᴰ.⟨ refl ⟩⋆⟨ f*aᴰ₂.βCL ⟩
                  ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆IdL _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩
                  ∙ (sym $ Cᴰ.⋆Assoc _ _ _))))
            ⟩
          ∙ (Cᴰ.≡in $ sym f*×.ηᴰCL)
      )
    where
    module f*× = CartesianLift (isFib (vertexⱽ bpⱽ) f)
    module f*aᴰ₁ = CartesianLift (isFib aᴰ₁ f)
    module f*aᴰ₂ = CartesianLift (isFib aᴰ₂ f)
    module bpⱽ = UniversalElementⱽNotation _ _ _ bpⱽ
    module bpⱽ' = BinProductⱽNotation bpⱽ
    module f*⟨aᴰ₁×aᴰ₂⟩ = PresheafNotation (BinProductProf Cᴰ.v[ b ] ⟅ f*aᴰ₁.f*yᴰ , f*aᴰ₂.f*yᴰ ⟆)
