module Cubical.Categories.Limits.BiCartesianClosed.Base where

open import Cubical.Categories.Category
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

record BiCartesianClosedCategory (ℓ ℓ' : Level) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  field
    CCC : CartesianClosedCategory ℓ ℓ'
  -- potential performance issue
  open CartesianClosedCategory CCC public
  field
    sums : BinCoProducts C

  open BinCoProductsNotation sums public
