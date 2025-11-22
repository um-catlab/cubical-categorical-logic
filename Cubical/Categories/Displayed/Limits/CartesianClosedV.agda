module Cubical.Categories.Displayed.Limits.CartesianClosedV where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

CartesianClosedCategoryⱽ : (CC : CartesianCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level) → Type _
CartesianClosedCategoryⱽ CC ℓCᴰ ℓCᴰ' =
  Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
  Σ[ termⱽ ∈ Terminalsⱽ Cᴰ ]
  Σ[ bpⱽ   ∈ BinProductsⱽ Cᴰ ]
  Σ[ cartesianLifts ∈ isFibration Cᴰ ]
  Σ[ expⱽ ∈ Exponentialsⱽ Cᴰ bpⱽ cartesianLifts ]
  UniversalQuantifiers Cᴰ bp cartesianLifts
  where
    open CartesianCategory CC

-- This is ungodly slow, why? exponential module stuff?
-- record CartesianClosedCategoryⱽ' (CC : CartesianCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
--   : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
--   no-eta-equality
--   constructor cartesiancategoryⱽ
--   open CartesianCategory CC public
--   field
--     Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
--     termⱽ : Terminalsⱽ Cᴰ
--     bpⱽ   : BinProductsⱽ Cᴰ
--     cartesianLifts : isFibration Cᴰ
--     expⱽ : Exponentialsⱽ Cᴰ bpⱽ cartesianLifts
--     ∀s   : UniversalQuantifiers Cᴰ bp cartesianLifts
--   module Cᴰ = Categoryᴰ Cᴰ

-- -- TODO: CartesianCategoryⱽ'→CartesianCategoryᴰ
