module Cubical.Categories.Instances.TotalCategory.Cartesian where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.CartesianD

import Cubical.Categories.Instances.TotalCategory as TC

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _
  {C : CartesianCategory ℓC ℓC'}
  (Cᴰ : CartesianCategoryᴰ C ℓCᴰ ℓCᴰ')
  where
  open CartesianCategory renaming (C to |C|)
  open CartesianCategoryᴰ renaming (Cᴰ to |Cᴰ|)
  open TerminalᴰNotation _ (Cᴰ .termᴰ)
  open BinProductsᴰNotation (Cᴰ .bpᴰ)

  ∫C : CartesianCategory _ _
  ∫C .|C| = TC.∫C (Cᴰ .|Cᴰ|)
  ∫C .term = ∫term
  ∫C .bp = ∫bp
