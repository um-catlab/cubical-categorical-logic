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
-- NOTE: The bottleneck is UniversalQuantifiers. Making that type
-- opaque gets rid of the speed issue
record CartesianClosedCategoryⱽ' (CC : CartesianCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  constructor cartesiancategoryⱽ
  open CartesianCategory CC public renaming (C to CartesianCat)
  field
    CartesianClosedCatᴰ : Categoryᴰ CartesianCat ℓCᴰ ℓCᴰ'
    termⱽ : Terminalsⱽ CartesianClosedCatᴰ
    bpⱽ   : BinProductsⱽ CartesianClosedCatᴰ
    cartesianLifts : isFibration CartesianClosedCatᴰ
    expⱽ : Exponentialsⱽ CartesianClosedCatᴰ bpⱽ cartesianLifts
    ∀s   : UniversalQuantifiers CartesianClosedCatᴰ bp cartesianLifts
  module Cᴰ = Categoryᴰ CartesianClosedCatᴰ

-- TODO: CartesianCategoryⱽ'→CartesianCategoryᴰ
