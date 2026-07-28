{-# OPTIONS --cubical --type-in-type #-}

module HyperDoc.Operational.Effects.DebugInsertAt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Properties
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
import Cubical.Data.Nat as Nat

insertAt :
  {X : Type} {n : ℕ} →
  Fin (suc n) → X → (Fin n → X) → Fin (suc n) → X
insertAt {X} {n} = Nat.elim base step n
  where
  base : Fin 1 → X → (Fin 0 → X) → Fin 1 → X
  base i x xs j with Iso.fun finSucMaybeIso j
  ... | nothing = x
  ... | just ()

  step :
    (n : ℕ) →
    (Fin (suc n) → X → (Fin n → X) → Fin (suc n) → X) →
    Fin (suc (suc n)) → X →
    (Fin (suc n) → X) → Fin (suc (suc n)) → X
  step n ih i x xs j
    with Iso.fun finSucMaybeIso i | Iso.fun finSucMaybeIso j
  ... | nothing | nothing = x
  ... | nothing | just j′ = xs j′
  ... | just i′ | nothing = xs zero
  ... | just i′ | just j′ =
    ih i′ x (λ k → xs (suc k)) j′

map-insertAt :
  ∀ {X Y : Type} {n : ℕ}
    (f : X → Y) (i : Fin (suc n)) x xs →
  (λ j → f (insertAt i x xs j))
    ≡ insertAt i (f x) (λ j → f (xs j))
map-insertAt {X} {Y} {n} f = Nat.elim base step n
  where
  base :
    (i : Fin 1) (x : X) (xs : Fin 0 → X) →
    (λ j → f (insertAt i x xs j))
      ≡ insertAt i (f x) (λ j → f (xs j))
  base i x xs =
    funExt λ j → lemma i x xs j
    where
    lemma : (i : Fin 1) (x : X) (xs : Fin 0 → X) (j : Fin 1) →
      f (insertAt {X = X} {n = 0} i x xs j)
        ≡ insertAt {X = Y} {n = 0} i (f x) (λ k → f (xs k)) j
    lemma i x xs j with Iso.fun finSucMaybeIso j
    ... | nothing = refl
    ... | just ()

  step :
    (n : ℕ) →
    ((i : Fin (suc n)) (x : X) (xs : Fin n → X) →
      (λ j → f (insertAt i x xs j))
        ≡ insertAt i (f x) (λ j → f (xs j))) →
    (i : Fin (suc (suc n))) (x : X) (xs : Fin (suc n) → X) →
    (λ j → f (insertAt i x xs j))
      ≡ insertAt i (f x) (λ j → f (xs j))
  step n ih i x xs =
    funExt λ j → lemma i x xs j
    where
    lemma :
      (i : Fin (suc (suc n))) (x : X)
      (xs : Fin (suc n) → X) (j : Fin (suc (suc n))) →
      f (insertAt {X = X} {n = suc n} i x xs j)
        ≡ insertAt {X = Y} {n = suc n}
            i (f x) (λ k → f (xs k)) j
    lemma i x xs j
      with Iso.fun finSucMaybeIso i | Iso.fun finSucMaybeIso j
    ... | nothing | nothing = refl
    ... | nothing | just j′ = refl
    ... | just i′ | nothing = refl
    ... | just i′ | just j′ =
      funExt⁻ (ih i′ x (λ k → xs (suc k))) j′

plugAt :
  {X : Type} {n : ℕ} →
  Fin n → X → (Fin (predℕ n) → X) → Fin n → X
plugAt {n = suc n} i = insertAt i
