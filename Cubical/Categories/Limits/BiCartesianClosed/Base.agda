module Cubical.Categories.Limits.BiCartesianClosed.Base where

open import Cubical.Categories.Category
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level

Initial' : (C : Category ℓ ℓ') → Type (ℓ-max ℓ ℓ')
Initial' C = Terminal' (C ^op)

record BiCartesianClosedCategory (ℓ ℓ' : Level) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  field
    CCC : CartesianClosedCategory ℓ ℓ'
  -- potential performance issue
  open CartesianClosedCategory CCC public
  field
    sums : BinCoProducts C
    init : Initial' C

  open BinCoProductsNotation sums public
