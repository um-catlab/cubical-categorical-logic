{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Reindex.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.Reindex.Base hiding (π)
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor
open UniversalElement
open UniversalElementᴰ
open UniversalElementᵛ
open CartesianLift

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where
  open isIsoOver
  private
    module C = Category C
    module D = Category D
    F*Dᴰ = reindex Dᴰ F
    module R = HomᴰReasoning Dᴰ
    module F*Dᴰ = Categoryᴰ F*Dᴰ
    module Dᴰ = Categoryᴰ Dᴰ
  preservesVerticalTerminal :
    ∀ c → VerticalTerminalAt Dᴰ (F ⟅ c ⟆)
    → VerticalTerminalAt (reindex Dᴰ F) c
  preservesVerticalTerminal c 𝟙ᴰ .vertexᴰ = 𝟙ᴰ .vertexᴰ
  preservesVerticalTerminal c 𝟙ᴰ .elementᴰ = 𝟙ᴰ .elementᴰ
  preservesVerticalTerminal c 𝟙ᴰ .universalᴰ .inv f _ = introᴰ 𝟙ᴰ (F ⟪ f ⟫) _
  preservesVerticalTerminal c 𝟙ᴰ .universalᴰ .rightInv _ _ = refl
  preservesVerticalTerminal c 𝟙ᴰ .universalᴰ {xᴰ = xᴰ} .leftInv f F⟪f⟫ᴰ = R.rectify $ R.≡out $
    (R.≡in $ congP (λ _ F⟪f⟫ → universalᴰ 𝟙ᴰ {xᴰ = xᴰ} .inv  F⟪f⟫ tt)
      (F .F-seq _ _ ∙ D.⟨ refl ⟩⋆⟨ F .F-id ⟩))
    ∙ sym (R.≡in $ ηᴰ 𝟙ᴰ)

  hasVerticalTerminals : VerticalTerminals Dᴰ →
    VerticalTerminals (reindex Dᴰ F)
  hasVerticalTerminals vtms c = preservesVerticalTerminal c (vtms (F ⟅ c ⟆))

  module _ {c : C .ob} {Fcᴰ Fcᴰ' : Dᴰ.ob[ F ⟅ c ⟆ ]}
    (vbp : VerticalBinProductsAt Dᴰ (Fcᴰ , Fcᴰ')) where
    private
      module Fcᴰ∧Fcᴰ' = VerticalBinProductsAtNotation vbp

    preservesVerticalBinProd : VerticalBinProductsAt (reindex Dᴰ F) (Fcᴰ , Fcᴰ')
    preservesVerticalBinProd .vertexᵛ = vbp .vertexᵛ
    preservesVerticalBinProd .elementᵛ .fst = R.reind (sym $ F .F-id) $ vbp .elementᵛ .fst
    preservesVerticalBinProd .elementᵛ .snd = R.reind (sym $ F .F-id) $ vbp .elementᵛ .snd
    preservesVerticalBinProd .universalᵛ .fst (fᴰ₁ , fᴰ₂) = fᴰ₁ Fcᴰ∧Fcᴰ'.,ᵛ fᴰ₂
    preservesVerticalBinProd .universalᵛ .snd .fst (fᴰ₁ , fᴰ₂) = ΣPathP
      ( (R.rectify $ R.≡out $
        (sym $ R.reind-filler _ _)
        ∙ (sym $ R.reind-filler _ _)
        ∙ R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
        ∙ R.reind-filler _ _
        ∙ R.≡in (Fcᴰ∧Fcᴰ'.×βᵛ₁ {fᴰ' = fᴰ₂}))
      , (R.rectify $ R.≡out $
        (sym $ R.reind-filler _ _)
        ∙ (sym $ R.reind-filler _ _)
        ∙ R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
        ∙ R.reind-filler _ _
        ∙ R.≡in (Fcᴰ∧Fcᴰ'.×βᵛ₂ {fᴰ = fᴰ₁})))
    preservesVerticalBinProd .universalᵛ .snd .snd fᴰ = R.rectify $ R.≡out $
      (R.≡in $ congP₂ (λ _ → Fcᴰ∧Fcᴰ'._,ᵛ_)
        (R.≡out $
          (sym $ R.reind-filler _ _)
          ∙ (sym $ R.reind-filler _ _)
          ∙ R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
          ∙ R.reind-filler _ _)
        (R.≡out $
          (sym $ R.reind-filler _ _)
          ∙ (sym $ R.reind-filler _ _)
          ∙ R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
          ∙ R.reind-filler _ _))
      ∙ sym (R.≡in $ Fcᴰ∧Fcᴰ'.×ηᵛ)

  hasVerticalBinProds : VerticalBinProducts Dᴰ →
    VerticalBinProducts (reindex Dᴰ F)
  hasVerticalBinProds vps Fcᴰ×Fcᴰ' =
    preservesVerticalBinProd (vps Fcᴰ×Fcᴰ')

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : CartesianCategoryⱽ D ℓDᴰ ℓDᴰ'}
  where

  isCartesianⱽReindex : isCartesianⱽ (reindex (Dᴰ .fst) F)
  isCartesianⱽReindex .fst = isFibrationReindex (Dᴰ .fst) F (Dᴰ .snd .fst)
  isCartesianⱽReindex .snd .fst = hasVerticalTerminals (Dᴰ .snd .snd .fst)
  isCartesianⱽReindex .snd .snd = hasVerticalBinProds (Dᴰ .snd .snd .snd)
