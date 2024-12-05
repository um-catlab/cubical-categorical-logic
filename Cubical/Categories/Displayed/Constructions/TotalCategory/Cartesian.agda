module Cubical.Categories.Displayed.Constructions.TotalCategory.Cartesian where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Categories.Displayed.Limits.Cartesian

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

module _ {C : CartesianCategory ℓC ℓC'}
  (Cᴰ : CartesianCategoryᴰ C ℓCᴰ ℓCᴰ')
  (Dᴰ : CartesianCategoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
  where
