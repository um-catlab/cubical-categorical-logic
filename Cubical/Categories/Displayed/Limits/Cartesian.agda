{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Agda.Builtin.Cubical.Equiv
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Foundations.Univalence

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
