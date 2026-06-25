-- Löb induction in the topos of trees (ℕ, <): guarded recursion and streams.
module Cubical.Categories.Direct.Instances.NatLobDemo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Recursive using (_<_ ; _≤_ ; ≤-refl)
open import Cubical.Data.List

open import Cubical.Categories.Direct.Instances.Poset using (löbWF)
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)

private
  variable
    A B C : Type

Stream : Type → Type
Stream A = ℕ → A

headₛ : Stream A → A
headₛ s = s 0

tailₛ : Stream A → Stream A
tailₛ s n = s (suc n)

cons : A → Stream A → Stream A
cons a s zero    = a
cons a s (suc n) = s n

mapₛ : (A → B) → Stream A → Stream B
mapₛ f s n = f (s n)

takeₛ : ℕ → Stream A → List A
takeₛ zero    _ = []
takeₛ (suc n) s = headₛ s ∷ takeₛ n (tailₛ s)

private
  k≤suc-k : ∀ k → k ≤ suc k
  k≤suc-k zero    = _
  k≤suc-k (suc k) = k≤suc-k k

  ℕSet : ℕ → hSet ℓ-zero
  ℕSet _ = ℕ , isSetℕ

nats : Stream ℕ
nats = löbWF ℕWFOrder ℕSet λ where
  zero    _   → 0
  (suc k) rec → suc (rec k (≤-refl k))

pow2 : Stream ℕ
pow2 = löbWF ℕWFOrder ℕSet λ where
  zero    _   → 1
  (suc k) rec → rec k (≤-refl k) + rec k (≤-refl k)

fibs : Stream ℕ
fibs = löbWF ℕWFOrder ℕSet λ where
  zero          _   → 0
  (suc zero)    _   → 1
  (suc (suc k)) rec → rec (suc k) (≤-refl k) + rec k (k≤suc-k k)

_ : takeₛ 6 nats ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
_ = refl

_ : takeₛ 6 pow2 ≡ 1 ∷ 2 ∷ 4 ∷ 8 ∷ 16 ∷ 32 ∷ []
_ = refl

_ : takeₛ 8 fibs ≡ 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ []
_ = refl

_ : fibs 6 ≡ 8
_ = refl

_ : takeₛ 0 nats ≡ []
_ = refl

_ : takeₛ 4 nats ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
_ = refl

_ : takeₛ 5 (tailₛ nats) ≡ takeₛ 5 (mapₛ suc nats)
_ = refl
