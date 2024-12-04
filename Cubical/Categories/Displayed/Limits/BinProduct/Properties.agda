{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.BinProduct.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
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
open UniversalElementᴰ
open isIsoOver

module _ {C : Category ℓC ℓC'}{x₁ x₂ : C .ob}
  (prod : BinProduct' C (x₁ , x₂))
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module c×c' = BinProduct'Notation prod
    module R = HomᴰReasoning Cᴰ

  open CartesianLift
  open UniversalElementᴰ

  module _ {xᴰ₁ : Cᴰ.ob[ x₁ ]}{xᴰ₂ : Cᴰ.ob[ x₂ ]}
    (lift-π₁ : CartesianLift Cᴰ xᴰ₁ c×c'.π₁)
    (lift-π₂ : CartesianLift Cᴰ xᴰ₂ c×c'.π₂)
    (vbp : VerticalBinProductsAt Cᴰ ((lift-π₁ .f*yᴰ) , (lift-π₂ .f*yᴰ)))
    where
    open VerticalBinProductsAtNotation vbp
    Vertical→LiftedBinProduct : LiftedBinProduct Cᴰ prod (xᴰ₁ , xᴰ₂)
    Vertical→LiftedBinProduct .vertexᴰ = vert
    Vertical→LiftedBinProduct .elementᴰ .fst = π₁ ⋆ᵛᴰ⟨ Cᴰ ⟩ (lift-π₁ .π)
    Vertical→LiftedBinProduct .elementᴰ .snd = π₂ ⋆ᵛᴰ⟨ Cᴰ ⟩ (lift-π₂ .π)
    Vertical→LiftedBinProduct .universalᴰ .inv (f₁ , f₂) (fᴰ₁ , fᴰ₂) =
      lift-π₁ .isCartesian .fst (R.reind (sym (c×c'.×β₁)) fᴰ₁)
      ,ᵛ lift-π₂ .isCartesian .fst (R.reind (sym (c×c'.×β₂)) fᴰ₂)
    -- β
    Vertical→LiftedBinProduct .universalᴰ .rightInv (f₁ , f₂) (fᴰ₁ , fᴰ₂) = ΣPathP
      ( (R.rectify $ R.≡out $
        sym (R.≡in (⋆Assocᴰᵛᴰ Cᴰ _ _ _))
        ∙ R.⟨ R.≡in ×βᵛ₁ ⟩⋆⟨ refl ⟩
        ∙ R.≡in (lift-π₁ .isCartesian .snd .fst (R.reind (sym (c×c'.×β₁)) fᴰ₁))
        ∙ sym (R.reind-filler _ _))
      , (R.rectify $ R.≡out $
        sym (R.≡in (⋆Assocᴰᵛᴰ Cᴰ _ _ _))
        ∙ R.⟨ R.≡in ×βᵛ₂ ⟩⋆⟨ refl ⟩
        ∙ R.≡in (lift-π₂ .isCartesian .snd .fst (R.reind (sym (c×c'.×β₂)) fᴰ₂))
        ∙ sym (R.reind-filler _ _)))
    -- η
    -- ( ⟨ fᴰ *ᴰ (π₁ ⋆ᵛᴰ lift-π₁.π ⟩π₁* ,v ⟨ fᴰ *ᵛ π₂ ⟩π₂*) ≡[ η ] fᴰ
    Vertical→LiftedBinProduct .universalᴰ .leftInv f fᴰ = R.rectify $ R.≡out $
      (R.≡in (cong₂ _,ᵛ_
        (cong (lift-π₁ .isCartesian .fst) (cong (R.reind (sym (c×c'.×β₁))) (symP $ ⋆Assocᴰᵛᴰ Cᴰ _ _ _)))
        (cong (lift-π₂ .isCartesian .fst) (cong (R.reind (sym (c×c'.×β₂))) (symP $ ⋆Assocᴰᵛᴰ Cᴰ _ _ _)))))
      ∙ R.≡in {p = sym c×c'.×η} (congP₂ (λ _ → _,ᵛ_)
                (congP (λ _ → lift-π₁ .isCartesian .fst) (R.rectify (R.≡out (sym (R.reind-filler (sym (c×c'.×β₁ )) (seqᴰᵛ Cᴰ fᴰ π₁ Cᴰ.⋆ᴰ lift-π₁ .π))))))
                (congP (λ _ → lift-π₂ .isCartesian .fst) (R.rectify (R.≡out (sym (R.reind-filler (sym (c×c'.×β₂ )) (seqᴰᵛ Cᴰ fᴰ π₂ Cᴰ.⋆ᴰ lift-π₂ .π)))))))
      ∙ R.≡in (congP₂ (λ _ → _,ᵛ_) (lift-π₁ .isCartesian .snd .snd (seqᴰᵛ Cᴰ fᴰ π₁)) (lift-π₂ .isCartesian .snd .snd (seqᴰᵛ Cᴰ fᴰ π₂)))
      ∙ R.≡in (symP ×ηᵛ)
