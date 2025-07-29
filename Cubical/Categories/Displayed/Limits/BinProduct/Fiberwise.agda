{-# OPTIONS --safe #-}
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
      using (v[_]; rectify; ≡out; ≡in; reind-filler; Hom[_][_,_]; _⋆ᴰ_; ⟨_⟩⋆⟨_⟩; ⋆Assoc; ⋆IdL; ⋆IdLᴰ)
  module _ {a} {aᴰ₁ aᴰ₂} (bpⱽ : BinProductⱽ Cᴰ (aᴰ₁ , aᴰ₂)) where
    private
      module a₁×ⱽa₂ = UniversalElementⱽNotation _ _ _ bpⱽ
        using (introⱽ; vertexⱽ; elementⱽ; βᴰ; introᴰ≡;
          module ∫ue)
      module a₁×ⱽa₂Pshⱽ = UniversalElementⱽNotation.Pshⱽ _ _ _ bpⱽ
        using (rectify; ≡out; ≡in)
    opaque
      binproduct-fiber-section-pf : ∀ Γᴰ → section
        (λ f →
           action Cᴰ.v[ a ] (BinProductProf Cᴰ.v[ a ] ⟅ aᴰ₁ , aᴰ₂ ⟆) f
           a₁×ⱽa₂.elementⱽ)
        (a₁×ⱽa₂.introⱽ {xᴰ = Γᴰ})
      binproduct-fiber-section-pf _ _ =
        a₁×ⱽa₂Pshⱽ.rectify $ a₁×ⱽa₂Pshⱽ.≡out $
          (a₁×ⱽa₂Pshⱽ.≡in {p = sym $ C.⋆IdL _} $ ΣPathP
            ( (Cᴰ.rectify $ Cᴰ.≡out $ sym $ Cᴰ.reind-filler _ _)
            , (Cᴰ.rectify $ (Cᴰ.≡out $ sym $ Cᴰ.reind-filler _ _))))
          ∙ (a₁×ⱽa₂.∫ue.β)

      binproduct-fiber-retract-pf : ∀ Γᴰ → retract
        (λ f →
           action Cᴰ.v[ a ] (BinProductProf Cᴰ.v[ a ] ⟅ aᴰ₁ , aᴰ₂ ⟆) f
           a₁×ⱽa₂.elementⱽ)
        (a₁×ⱽa₂.introⱽ {xᴰ = Γᴰ})
      binproduct-fiber-retract-pf _ _ = Cᴰ.rectify $ Cᴰ.≡out $
        a₁×ⱽa₂.introᴰ≡ $ a₁×ⱽa₂Pshⱽ.≡in {p = sym $ C.⋆IdR _} $ ΣPathP
          ( (Cᴰ.rectify $ Cᴰ.≡out $ sym $ Cᴰ.reind-filler _ _)
          , (Cᴰ.rectify $ Cᴰ.≡out $ sym $ Cᴰ.reind-filler _ _))

    BinProductⱽ→BinProductFiber : BinProduct'' Cᴰ.v[ a ] (aᴰ₁ , aᴰ₂)
    BinProductⱽ→BinProductFiber .vertex = a₁×ⱽa₂.vertexⱽ
    BinProductⱽ→BinProductFiber .element = a₁×ⱽa₂.elementⱽ
    BinProductⱽ→BinProductFiber .universal Γᴰ =
      isIsoToIsEquiv ( a₁×ⱽa₂.introⱽ
        , binproduct-fiber-section-pf Γᴰ
        , binproduct-fiber-retract-pf Γᴰ
        )

  hasAllBinProductⱽ→BinProductFibers :
    ∀ {a} → hasAllBinProductⱽ Cᴰ → BinProducts'' Cᴰ.v[ a ]
  hasAllBinProductⱽ→BinProductFibers bpⱽ (aᴰ₁ , aᴰ₂) =
    BinProductⱽ→BinProductFiber (bpⱽ (aᴰ₁ , aᴰ₂))

  module _
    {a b aᴰ₁ aᴰ₂}
    (isFib : isFibration Cᴰ)
    (bpⱽ : BinProductⱽ Cᴰ (aᴰ₁ , aᴰ₂))
    (f : C [ b , a ]) where

    private
      module f*× = CartesianLift (isFib (vertexⱽ bpⱽ) f)
      module f*aᴰ₁ = CartesianLift (isFib aᴰ₁ f)
      module f*aᴰ₂ = CartesianLift (isFib aᴰ₂ f)
      module bpⱽ = UniversalElementⱽNotation _ _ _ bpⱽ
        using (introᴰ; elementⱽ; introᴰ≡)
      module bpⱽ' = BinProductⱽNotation bpⱽ
        using (×βⱽ₁; ×βⱽ₂)

    intro-f*× : ∀ bᴰ →
      Σ Cᴰ.Hom[ C.id ][ bᴰ , f*aᴰ₁.f*yᴰ ]
      (λ _ → Cᴰ.Hom[ C.id ][ bᴰ , f*aᴰ₂.f*yᴰ ]) →
      Cᴰ.Hom[ C.id ][ bᴰ , f*×.f*yᴰ ]
    intro-f*× bᴰ (fⱽ₁ , fⱽ₂) =
      f*×.introCL (bpⱽ.introᴰ _ ((fⱽ₁ Cᴰ.⋆ᴰ f*aᴰ₁.π) , (fⱽ₂ Cᴰ.⋆ᴰ f*aᴰ₂.π)))

    opaque

      intro-f*×-retract : ∀ {bᴰ} →
        retract
          (λ f₁ →
           action Cᴰ.v[ b ]
           (BinProductProf Cᴰ.v[ b ] ⟅
            CartesianLiftF-fiber Cᴰ isFib f ⟅ aᴰ₁ ⟆ ,
            CartesianLiftF-fiber Cᴰ isFib f ⟅ aᴰ₂ ⟆
            ⟆)
           f₁
           (CartesianLiftF-fiber Cᴰ isFib f ⟪ bpⱽ.elementⱽ .fst ⟫ ,
            CartesianLiftF-fiber Cᴰ isFib f ⟪ bpⱽ.elementⱽ .snd ⟫))
          (intro-f*× bᴰ)
      intro-f*×-retract fⱽ =
        Cᴰ.rectify $ Cᴰ.≡out $
          f*×.introCL⟨ refl ⟩⟨
            bpⱽ.introᴰ≡ (ΣPathP $
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

      intro-f*×-section : ∀ {bᴰ} →
        section
          (λ f₁ →
           action Cᴰ.v[ b ]
           (BinProductProf Cᴰ.v[ b ] ⟅
            CartesianLiftF-fiber Cᴰ isFib f ⟅ aᴰ₁ ⟆ ,
            CartesianLiftF-fiber Cᴰ isFib f ⟅ aᴰ₂ ⟆
            ⟆)
           f₁
           (CartesianLiftF-fiber Cᴰ isFib f ⟪ bpⱽ.elementⱽ .fst ⟫ ,
            CartesianLiftF-fiber Cᴰ isFib f ⟪ bpⱽ.elementⱽ .snd ⟫))
          (intro-f*× bᴰ)
      intro-f*×-section (fⱽ₁ , fⱽ₂) = ΣPathP
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
        )

    cartesianLift-preserves-BinProductFiber :
      preservesBinProduct' (CartesianLiftF-fiber Cᴰ isFib f)
                           (BinProductⱽ→BinProductFiber bpⱽ)
    cartesianLift-preserves-BinProductFiber bᴰ = isIsoToIsEquiv
      ( intro-f*× bᴰ
      , intro-f*×-section
      , intro-f*×-retract)

