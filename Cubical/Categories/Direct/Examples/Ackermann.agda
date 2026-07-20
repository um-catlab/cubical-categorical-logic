{-# OPTIONS --lossy-unification #-}
-- The Ackermann function by Löb induction over the lexicographic order on ℕ × ℕ
module Cubical.Categories.Direct.Examples.Ackermann where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hSet)
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma using (_×_ ; _,_)
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Nat.Order.Recursive using (≤-refl)
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Product using (LexWFOrder)
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)
open import Cubical.Categories.Direct.Instances.Poset using (PosetDirect)
open import Cubical.Categories.Direct.StrictDownset
  using (▷Fam ; ▷FamApp ; löbFam ; löbFam-unfold)

private
  dir = PosetDirect (LexWFOrder ℕWFOrder ℕWFOrder)

open DirectNotation dir using (_≺_)

lex-fst : ∀ {m n n'} → (m , n) ≺ (suc m , n')
lex-fst {m} = inl (≤-refl m)

lex-snd : ∀ {m n} → (m , n) ≺ (m , suc n)
lex-snd {_} {n} = inr (Eq.refl , ≤-refl n)

A : ℕ × ℕ → hSet ℓ-zero
A _ = ℕ , isSetℕ

call : ∀ {x} → ⟨ ▷Fam dir {ℓF = ℓ-zero} A x ⟩ → ∀ y → y ≺ x → ℕ
call β y q = ▷FamApp dir {ℓF = ℓ-zero} A β (inl q) q

step : ∀ x → ⟨ ▷Fam dir {ℓF = ℓ-zero} A x ⟩ → ⟨ A x ⟩
step (zero  , n)     β = suc n
step (suc m , zero)  β = call β (m , 1) lex-fst
step (suc m , suc n) β = call β (m , call β (suc m , n) lex-snd) lex-fst

ack : ℕ → ℕ → ℕ
ack m n = löbFam dir {ℓF = ℓ-zero} A step (m , n)

ack-0 : ∀ n → ack 0 n ≡ suc n
ack-0 n = löbFam-unfold dir {ℓF = ℓ-zero} A step (0 , n)

ack-s0 : ∀ m → ack (suc m) 0 ≡ ack m 1
ack-s0 m = löbFam-unfold dir {ℓF = ℓ-zero} A step (suc m , 0)

ack-ss : ∀ m n → ack (suc m) (suc n) ≡ ack m (ack (suc m) n)
ack-ss m n = löbFam-unfold dir {ℓF = ℓ-zero} A step (suc m , suc n)

_ : ack 4 0 ≡ 13
_ = refl

_ : ack 2 4 ≡ 11
_ = refl

_ : ack 3 3 ≡ 61
_ = refl
