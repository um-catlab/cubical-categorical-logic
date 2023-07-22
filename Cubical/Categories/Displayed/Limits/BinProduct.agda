{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where
  module D = Categoryᴰ D
  BinProductᴰ : ∀ {c12} → BinProduct' C c12
              → (D.ob[ c12 .fst ] × D.ob[ c12 .snd ])
              → Type _
  BinProductᴰ = RightAdjointAtᴰ (ΔCᴰ D)

  BinProductsᴰ : BinProducts' C → Type _
  BinProductsᴰ = RightAdjointᴰ (ΔCᴰ D)

  FibBinProductsAtᴰ : ∀ {c} → (D.ob[ c ] × D.ob[ c ]) → Type _
  FibBinProductsAtᴰ = LocalRightAdjointAtᴰ (Δᴰ D)

  FibBinProductsᴰ : Type _
  FibBinProductsᴰ = LocalRightAdjointᴰ (Δᴰ D)
