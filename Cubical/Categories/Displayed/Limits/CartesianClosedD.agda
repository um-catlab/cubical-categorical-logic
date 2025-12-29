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

record CartesianClosedCategoryᴰ (CCC : CartesianClosedCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level) : Type ((ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓC) (ℓ-suc ℓC')) (ℓ-suc ℓCᴰ)) (ℓ-suc ℓCᴰ'))) where
  open CartesianClosedCategory CCC
  field
    CCᴰ : CartesianCategoryᴰ CC ℓCᴰ ℓCᴰ'

  open CartesianCategoryᴰ CCᴰ public
  field
    expᴰ : AllExponentiableᴰ Cᴰ bp bpᴰ exps

  open ExponentialsᴰNotation {C = C}{Cᴰ = Cᴰ} bp bpᴰ exps expᴰ public
