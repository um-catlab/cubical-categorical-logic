{-# OPTIONS --safe #-}
-- the product of two cartesian categories is cartesian
module Cubical.Categories.Constructions.BinProduct.Cartesian where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Constructions.TotalCategory.Cartesian
import Cubical.Categories.Constructions.BinProduct as BP

open import Cubical.Categories.Displayed.Constructions.Weaken.Cartesian

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _
  (C : CartesianCategory ℓC ℓC')
  (D : CartesianCategory ℓD ℓD')
  where
  _×C_ : CartesianCategory _ _
  _×C_ = ∫C (weaken C D)
  private
    test : _×C_ .fst ≡ C .fst BP.×C D .fst
    test = refl
