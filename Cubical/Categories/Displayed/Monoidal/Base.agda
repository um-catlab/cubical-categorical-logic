-- Displayed monoidal categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Displayed.Monoidal.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalIsomorphism
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More

private
  variable
    ℓM ℓM' ℓMᴰ ℓMᴰ' : Level
module _ (M : MonoidalCategory ℓM ℓM') where
  private
    module M = MonoidalCategory M
  module _ (Cᴰ : Categoryᴰ M.C ℓMᴰ ℓMᴰ') where
    private
      module Cᴰ = Categoryᴰ Cᴰ
    record TensorStrᴰ : Type (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓMᴰ ℓMᴰ')) where
      field
        ─⊗ᴰ─ : Functorᴰ M.─⊗─ (Cᴰ ×Cᴰ Cᴰ) Cᴰ
        unitᴰ : Cᴰ.ob[ M.unit ]
    record MonoidalStrᴰ : Type (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓMᴰ ℓMᴰ')) where
      field
        tenstrᴰ : TensorStrᴰ
      open TensorStrᴰ tenstrᴰ public
      field
        αᴰ : NatIsoᴰ M.α
               (─⊗ᴰ─ ∘Fᴰ (𝟙ᴰ⟨ Cᴰ ⟩ ×Fᴰ ─⊗ᴰ─))
               (─⊗ᴰ─ ∘Fᴰ ((─⊗ᴰ─ ×Fᴰ 𝟙ᴰ⟨ Cᴰ ⟩) ∘Fᴰ {!×C-assoc!}))
