-- technically exponentials aren't a limits so find a better home for this
module Cubical.Categories.Displayed.Limits.CartesianClosedD where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

-- CartesianClosedCategoryᴰ : (CCC : CartesianClosedCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level) → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓC) (ℓ-suc ℓC')) (ℓ-suc ℓCᴰ)) (ℓ-suc ℓCᴰ'))
-- CartesianClosedCategoryᴰ CCC ℓCᴰ ℓCᴰ' =
--   Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
--   Σ[ termᴰ ∈ Terminalᴰ Cᴰ term ]
--   Σ[ bpᴰ ∈ BinProductsᴰ Cᴰ bp ]
--
--   where open CartesianClosedCategory CCC

module _ (CCC : CartesianClosedCategory ℓC ℓC') (CCCⱽ : CartesianClosedCategoryⱽ (CartesianClosedCategory.CC CCC) ℓCᴰ ℓCᴰ') where
  open CartesianClosedCategoryᴰ
  CartesianClosedCategoryⱽ→CartesianClosedCategoryᴰ : CartesianClosedCategoryᴰ CCC ℓCᴰ ℓCᴰ'
  CartesianClosedCategoryⱽ→CartesianClosedCategoryᴰ .CCᴰ = CartesianCategoryⱽ→CartesianCategoryᴰ (CartesianClosedCategory.CC CCC) {!!}
  CartesianClosedCategoryⱽ→CartesianClosedCategoryᴰ .expᴰ = {!!}
