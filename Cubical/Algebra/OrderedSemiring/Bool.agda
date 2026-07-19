-- The Boolean ordered semiring
module Cubical.Algebra.OrderedSemiring.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Algebra.OrderedSemiring

private
  ∨-assoc : ∀ x y z → (x or y) or z ≡ x or (y or z)
  ∨-assoc false y z = refl
  ∨-assoc true  y z = refl

  ∨-comm : ∀ x y → x or y ≡ y or x
  ∨-comm false false = refl
  ∨-comm false true  = refl
  ∨-comm true  false = refl
  ∨-comm true  true  = refl

  ∨-idem : ∀ x → x or x ≡ x
  ∨-idem false = refl
  ∨-idem true  = refl

  ∧-assoc : ∀ x y z → (x and y) and z ≡ x and (y and z)
  ∧-assoc false y z = refl
  ∧-assoc true  y z = refl

  ∧-idr : ∀ x → x and true ≡ x
  ∧-idr false = refl
  ∧-idr true  = refl

  ∧-distribˡ : ∀ x y z → (x or y) and z ≡ (x and z) or (y and z)
  ∧-distribˡ false y     z     = refl
  ∧-distribˡ true  y     true  = refl
  ∧-distribˡ true  false false = refl
  ∧-distribˡ true  true  false = refl

Boolean : OrderedSemiring ℓ-zero
Boolean = record
  { R          = Bool     ; isSetR = isSetBool
  ; 𝟘          = false    ; 𝟙 = true
  ; _⊕_        = _or_     ; _⊗_ = _and_
  ; ⊕-assoc    = ∨-assoc  ; ⊕-comm = ∨-comm ; ⊕-idem = ∨-idem
  ; ⊕-unit     = λ _ → refl
  ; ⊗-assoc    = ∧-assoc  ; ⊗-unitˡ = λ _ → refl ; ⊗-unitʳ = ∧-idr
  ; ⊗-annihilˡ = λ _ → refl
  ; ⊗-distribˡ = ∧-distribˡ
  }

open import Cubical.Algebra.OrderedSemiring.Selective
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)

private
  ∨-select : ∀ x y → (x or y ≡ x) ⊎ (x or y ≡ y)
  ∨-select false y = inr refl
  ∨-select true  y = inl refl

BooleanSel : SelectiveSemiring ℓ-zero
BooleanSel = record { semiring = Boolean ; ⊕-select = ∨-select }
