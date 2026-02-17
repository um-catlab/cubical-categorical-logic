{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Exponentials.CartesianClosed where

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Displayed.Exponentials.Base
open import Cubical.Categories.Displayed.Limits.CartesianD
open import Cubical.Categories.Displayed.Limits.CartesianV
open import Cubical.Categories.Displayed.Quantifiers

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open CartesianClosedCategory hiding (_×_)
open CartesianCategoryᴰ
open CartesianCategory hiding (_×_)
CartesianClosedCategoryᴰ : (CCC : CartesianClosedCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level) → Type _
CartesianClosedCategoryᴰ CCC ℓCᴰ ℓCᴰ' =
  Σ[ CCᴰ ∈ CartesianCategoryᴰ (CCC .CC) ℓCᴰ ℓCᴰ' ]
  Exponentialsᴰ
    (CCᴰ .Cᴰ)
    (CCC .CC .bp)
    (CCC .exps)
    (CCᴰ .bpᴰ)

open CartesianCategoryⱽ
CartesianClosedCategoryⱽ :
  Category ℓC ℓC' → (ℓCᴰ ℓCᴰ' : Level) → Type _
CartesianClosedCategoryⱽ C ℓCᴰ ℓCᴰ' =
  Σ[ CCⱽ ∈ CartesianCategoryⱽ C ℓCᴰ ℓCᴰ' ]
  Σ[ bp ∈ BinProducts C ]
  Exponentialsⱽ (Cᴰ CCⱽ) (bpⱽ CCⱽ) (CCⱽ .cartesianLifts)
  × UniversalQuantifiers bp (CCⱽ .cartesianLifts)
