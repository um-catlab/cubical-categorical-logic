{-
  Cartesian Fibrations, the fiberwise analogue of cartesian categories
-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.CartesianFibration where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Fibration.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

isCartesianFibration : {C : Category ℓC ℓC'}(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
isCartesianFibration Cᴰ =
  isFibration Cᴰ
  × VerticalTerminals Cᴰ
  × VerticalBinProducts Cᴰ

-- closed under reindexing

-- closed under ∫ᴰ
