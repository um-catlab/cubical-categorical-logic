module Cubical.Categories.Displayed.Limits.CartesianClosedV where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

CartesianClosedCategoryⱽ : (CC : CartesianCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level) → Type _
CartesianClosedCategoryⱽ CC ℓCᴰ ℓCᴰ' =
  Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
  Σ[ cartLifts ∈ isFibration Cᴰ ]
  Σ[ termⱽ ∈ Terminalsⱽ Cᴰ ]
  Σ[ bpⱽ ∈ BinProductsⱽ Cᴰ ]
  -- AllLRⱽ is technically redundant with cartLifts+bpⱽ, but I will
  -- keep it for now because the reindexing theorem depends on it
  Σ[ lrⱽ ∈ AllLRⱽ Cᴰ ]
  Σ[ expⱽ ∈ Exponentialsⱽ Cᴰ lrⱽ ]
  UniversalQuantifiers Cᴰ bp cartLifts
  where
    open CartesianCategory CC

-- This is ungodly slow, likely due to exponential module stuff.
--
-- I'm leaving it here because it would probably be an informative
-- example for profiling exponential module blowups.

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
