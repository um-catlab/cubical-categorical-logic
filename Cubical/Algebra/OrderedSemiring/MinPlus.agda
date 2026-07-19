-- The min-plus (tropical) ordered semiring
module Cubical.Algebra.OrderedSemiring.MinPlus where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero)
open import Cubical.Data.Maybe using (just)
open import Cubical.Data.Nat.More
open import Cubical.Algebra.OrderedSemiring

MinPlus : OrderedSemiring ℓ-zero
MinPlus = record
  { R          = Cost      ; isSetR = isSetCost
  ; 𝟘          = ∞         ; 𝟙 = just zero
  ; _⊕_        = _⊕_       ; _⊗_ = _⊗_
  ; ⊕-assoc    = ⊕-assoc   ; ⊕-comm = ⊕-comm ; ⊕-idem = ⊕-idem
  ; ⊕-unit     = λ _ → refl
  ; ⊗-assoc    = ⊗-assoc   ; ⊗-unitˡ = ⊗-unitˡ ; ⊗-unitʳ = ⊗-unitʳ
  ; ⊗-annihilˡ = λ _ → refl
  ; ⊗-distribˡ = ⊗-distribˡ
  }

open import Cubical.Algebra.OrderedSemiring.Selective

MinPlusSel : SelectiveSemiring ℓ-zero
MinPlusSel = record { semiring = MinPlus ; ⊕-select = ⊕-select }
