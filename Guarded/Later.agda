{-# OPTIONS --cubical --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Guarded.Later where

-- | This file is adapted from the supplementary material for the
-- | paper https://doi.org/10.1145/3372885.3373814, originally written
-- | by Niccolò Veltri and Andrea Vezzosi see the LICENSE.txt for
-- | their license.

open import Agda.Builtin.Equality renaming (_≡_ to _≣_) hiding (refl)
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Clock : Set
  Tick : Clock → LockU

private
  variable
    l : Level
    l' : Level
    A : Set l
    B : Set l'
    k : Clock

▹_,_ : Clock → Set l → Set l
▹ k , A = (@tick t : Tick k) → A

▸_ : ▹ k , Set l → Set l
▸ A = (@tick t : Tick _) → A t

next : A → ▹ k , A
next x _ = x

_⊛_ : ▹ k , (A → B) → ▹ k , A → ▹ k , B
_⊛_ f x a = f a (x a)

map▹ : (f : A → B) → ▹ k , A → ▹ k , B
map▹ f x α = f (x α)
_<$>_ = map▹

-- The behaviour of fix is encoded with rewrite rules, following the
-- definitional equalities of Clocked CTT.
postulate
  dfix : ∀ {k}{l} {A : Set l} → (f : ▹ k , A → A) → I → ▹ k , A
  dfix-beta : ∀ {l} {A : Set l} → (f : ▹ k , A → A) → dfix f i1 ≣ next (f (dfix f i0))

{-# REWRITE dfix-beta #-}

pfix : ∀ {l} {A : Set l} → (f : ▹ k , A → A) → dfix f i0 ≡ next (f (dfix f i0))
pfix f i = dfix f i

abstract
  fix : ∀ {l} {A : Set l} → (f : ▹ k , A → A) → A
  fix f = f (pfix f i0)

  fix-eq : ∀ {l} {A : Set l} → (f : ▹ k , A → A) → fix f ≡ f (next (fix f))
  fix-eq f = cong f (pfix f)

later-ext : ∀ {ℓ : Level} -> {A : ▹ k , Type ℓ} → {f g : ▸ A} → (▸ \ a → f a ≡ g a) → f ≡ g
later-ext eq i a = eq a i

transpLater : ∀ (A : I → ▹ k , Set) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 a = transp (\ i → A i a) i0 (u0 a)

hcompLater : ∀ (A : ▹ k , Set) φ (u : I → Partial φ (▸ A)) → (u0 : ▸ A [ φ ↦ u i0 ]) → ▸ A
hcompLater A φ u u0 a = hcomp (\ { i (φ = i1) → u i 1=1 a }) (outS u0 a)

postulate
  force : (∀ k → (▹ k , A)) → (∀ (k : Clock) → A)

postulate
  force-beta : ∀ {A : Set l} (x : A) → force (λ k _ → x) ≣ λ k → x

