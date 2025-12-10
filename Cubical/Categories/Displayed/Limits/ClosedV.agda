module Cubical.Categories.Displayed.Limits.ClosedV where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

ClosedCategoryⱽ : (CC : CartesianCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level) → Type _
ClosedCategoryⱽ CC ℓCᴰ ℓCᴰ' =
  Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
  Σ[ lrⱽ ∈ AllLRⱽ Cᴰ ]
  Σ[ lr∀ ∈ AllLR∀ Cᴰ bp ]
  Σ[ expⱽ ∈ Exponentialsⱽ Cᴰ lrⱽ ]
  UniversalQuantifiers Cᴰ bp lr∀
  where
    open CartesianCategory CC
