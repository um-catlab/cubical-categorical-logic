{-# OPTIONS --cubical --type-in-type #-}

module HyperDoc.Algebra.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.FinData
open import Cubical.Data.Nat

record Signature : Set₁ where
  field
    Op    : Set
    arity : Op → ℕ

open Signature public

IsAlg : (Σ : Signature) → hSet _ → Type
IsAlg Σ X =
  (o : Op Σ) → (Fin (arity Σ o) → ⟨ X ⟩) → ⟨ X ⟩

record Alg (Σ : Signature) : Set₁ where
  field
    Carrier : hSet _
    interp  : IsAlg Σ Carrier

open Alg public

IsAlgHom :
  {Σ : Signature} {M N : Alg Σ} →
  (⟨ Carrier M ⟩ → ⟨ Carrier N ⟩) → Type
IsAlgHom {Σ} {M} {N} f =
  ∀ (o : Op Σ) (args : Fin (arity Σ o) → ⟨ Carrier M ⟩) →
    f (interp M o args) ≡ interp N o (λ i → f (args i))

data FreeOn (Σ : Signature) (X : Type) : Type where
  inc : X → FreeOn Σ X
  ops :
    (o : Op Σ) →
    (Fin (arity Σ o) → FreeOn Σ X) →
    FreeOn Σ X
