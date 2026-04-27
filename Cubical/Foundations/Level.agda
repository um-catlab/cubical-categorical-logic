module Cubical.Foundations.Level where

open import Cubical.Foundations.Prelude

_⊔_ : Level → Level → Level
_⊔_ = ℓ-max

infixl 8 _⊔_
