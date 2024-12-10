{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryR.Cartesian where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Constructions.BinProduct.Cartesian

open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Constructions.TotalCategory.Cartesian
open import Cubical.Categories.Displayed.Constructions.Weaken.Cartesian

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

module _
  (C : CartesianCategory ℓC ℓC')
  (D : CartesianCategory ℓD ℓD')
  (Cᴰ : CartesianCategoryᴰ (C ×C D) ℓCᴰ ℓCᴰ')
  where
  ∫Cᴰsr : CartesianCategoryᴰ C _ _
  ∫Cᴰsr = ∫Cᴰ (weaken C D) Cᴰ
