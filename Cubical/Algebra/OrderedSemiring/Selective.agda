module Cubical.Algebra.OrderedSemiring.Selective where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Algebra.OrderedSemiring

record SelectiveSemiring (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    semiring : OrderedSemiring ℓ
  open OrderedSemiring semiring public
  field
    ⊕-select : ∀ x y → (x ⊕ y ≡ x) ⊎ (x ⊕ y ≡ y)
