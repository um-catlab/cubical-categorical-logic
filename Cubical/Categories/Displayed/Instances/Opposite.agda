{-
   Doubly Displayed Opposite Category.

   The fact that we have to do this is a big downside of making Categoryᴰ no-eta-equality

-}
module Cubical.Categories.Displayed.Instances.Opposite where

open import Cubical.Foundations.Prelude
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.TotalCategory.More
open import Cubical.Categories.Displayed.Instances.Reindex.Eq.Base

_^opᴰᴰ : ∀ {ℓ ℓ' ℓᴰ ℓᴰ' ℓᴰᴰ ℓᴰᴰ'} {C : Category ℓ ℓ'}{Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  (Cᴰᴰ : Categoryᴰ (∫C Cᴰ) ℓᴰᴰ ℓᴰᴰ') → Categoryᴰ (∫C (Cᴰ ^opᴰ)) ℓᴰᴰ ℓᴰᴰ'
Cᴰᴰ ^opᴰᴰ =
  EqReindex.reindex (Cᴰᴰ ^opᴰ) ∫C-op-commute⁻ Eq.refl λ _ _ → Eq.refl
