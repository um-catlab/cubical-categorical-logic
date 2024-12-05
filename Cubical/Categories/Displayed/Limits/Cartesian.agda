{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Representable


open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Fibration.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

CartesianCategoryᴰ : CartesianCategory ℓC ℓC' → (ℓCᴰ ℓCᴰ' : Level) → Type _
CartesianCategoryᴰ (C , term , bps) ℓCᴰ ℓCᴰ' =
  Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
  LiftedTerminal Cᴰ term'
  × LiftedBinProducts Cᴰ bps'
  where
  term' : _
  term' = terminalToUniversalElement term

  bps' : BinProducts' C
  bps' = BinProductsToBinProducts' C bps

isCartesianⱽ : ∀ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') → Type _
isCartesianⱽ Cᴰ = isFibration Cᴰ × VerticalTerminals Cᴰ × VerticalBinProducts Cᴰ

CartesianCategoryⱽ : Category ℓC ℓC' → (ℓCᴰ ℓCᴰ' : Level) → Type _
CartesianCategoryⱽ C ℓCᴰ ℓCᴰ' = Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ] isCartesianⱽ Cᴰ

open BinProduct
CartesianCategoryⱽ→CartesianCategoryᴰ :
  ∀ (C : CartesianCategory ℓC ℓC')
  → (Cᴰ : CartesianCategoryⱽ (C .fst) ℓCᴰ ℓCᴰ')
  → CartesianCategoryᴰ C ℓCᴰ ℓCᴰ'
CartesianCategoryⱽ→CartesianCategoryᴰ (C , term , bp) (Cᴰ , isFibCᴰ , termⱽ , bpⱽ) =
  Cᴰ
  , Vertical/𝟙→LiftedTerm Cᴰ (termⱽ _)
  , λ (xᴰ , yᴰ) → Vertical→LiftedBinProduct (BinProductsToBinProducts' C bp _)
      Cᴰ
      (isFibCᴰ _ _)
      (isFibCᴰ _ _)
      (bpⱽ _)
