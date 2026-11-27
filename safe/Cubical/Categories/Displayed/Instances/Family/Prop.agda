module Cubical.Categories.Displayed.Instances.Family.Prop where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Family.Base

PROPᴰ : ∀ ℓ → Categoryᴰ (SET ℓ) (ℓ-suc ℓ) ℓ
PROPᴰ ℓ = Fam (PROP ℓ)
