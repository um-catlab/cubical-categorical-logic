{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Limits.CartesianV' where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
import Cubical.Categories.Displayed.Presheaf.Representable as Curried
open import Cubical.Categories.Displayed.Limits.CartesianD

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

record CartesianCategoryⱽ (C : Category ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    termⱽ : Terminalsⱽ Cᴰ
    bpⱽ   : BinProductsⱽ Cᴰ
    cartesianLifts : isFibration Cᴰ
  module Cᴰ = Categoryᴰ Cᴰ

-- TODO: CartesianCategoryⱽ'→CartesianCategoryᴰ
-- CartesianCategoryⱽ→CartesianCategoryᴰ :
--   ∀ (CC : CartesianCategory ℓC ℓC')
--   → CartesianCategoryⱽ (CC .CartesianCategory.C) ℓCᴰ ℓCᴰ'
--   → CartesianCategoryᴰ CC ℓCᴰ ℓCᴰ'
-- CartesianCategoryⱽ→CartesianCategoryᴰ CC CCⱽ =
--   cartesiancategoryᴰ Cᴰ
--     {!!}
--     {!!}
--   where
--     open CartesianCategoryⱽ CCⱽ
