module Cubical.Categories.Instances.Thin where

open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Equiv.Properties
-- open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

-- open import Cubical.Data.Unit
-- open import Cubical.Data.Sigma

open import Cubical.Categories.Category
-- open import Cubical.Categories.HLevels
-- open import Cubical.Categories.Functor
-- open import Cubical.Categories.NaturalTransformation

private
  variable ℓ ℓ' : Level

open Category

ThinCategory :
  (A : Type ℓ)
  (_≤_ : A → A → Type ℓ')
  (rfl : ∀ {a} → a ≤ a)
  (trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
  (isProp≤ : ∀ {a b} → isProp (a ≤ b))
  → Category ℓ ℓ'
ThinCategory A _≤_ rfl trans isProp≤ .ob = A
ThinCategory A _≤_ rfl trans isProp≤ .Hom[_,_] = _≤_
ThinCategory A _≤_ rfl trans isProp≤ .id = rfl
ThinCategory A _≤_ rfl trans isProp≤ ._⋆_ = trans
ThinCategory A _≤_ rfl trans isProp≤ .⋆IdL _ = isProp≤ _ _
ThinCategory A _≤_ rfl trans isProp≤ .⋆IdR _ = isProp≤ _ _
ThinCategory A _≤_ rfl trans isProp≤ .⋆Assoc _ _ _ = isProp≤ _ _
ThinCategory A _≤_ rfl trans isProp≤ .isSetHom = isProp→isSet $ isProp≤
