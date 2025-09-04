-- The product of two cartesian categories is cartesian
module Cubical.Categories.Constructions.BinProduct.Cartesian where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Categories.Constructions.TotalCategory.Cartesian

open import Cubical.Categories.Displayed.Constructions.Weaken.Properties

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _
  (C : CartesianCategory ℓC ℓC')
  (D : CartesianCategory ℓD ℓD')
  where
  _×_ : CartesianCategory _ _
  _×_ = ∫C (weakenCartesianCategory C D)
