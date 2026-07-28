{-# OPTIONS --cubical --type-in-type #-}

module HyperDoc.Operational.Effects.Reduction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

------------------------------------------------------------------------
-- Section 1: inputs

record Signature : Type where
  field
    Op    : Type
    arity : Op → ℕ

open Signature

data Term (Σ : Signature) (X : Type) : Type where
  var : X → Term Σ X
  op  : (o : Op Σ) → (Fin (arity Σ o) → Term Σ X) → Term Σ X

record Polynomial : Type where
  constructor _◂_
  field
    Shape : Type
    size  : Shape → ℕ

open Polynomial

⟦_⟧ : Polynomial → Type → Type
⟦ P ⟧ X = Σ[ s ∈ Shape P ] (Fin (size P s) → X)

mapP : ∀ {P X Y} → (X → Y) → ⟦ P ⟧ X → ⟦ P ⟧ Y
mapP f (s , xs) = s , λ i → f (xs i)

-- A parametric, proposition-valued relation on the interpretation of p.
Relation : Polynomial → Type
Relation P =
  (X : hSet ℓ-zero) → (u v : ⟦ P ⟧ ⟨ X ⟩) → hProp ℓ-zero

SectionAt :
  (P : Polynomial) (Q : hSet ℓ-zero → hSet ℓ-zero) →
  hSet ℓ-zero → Type
SectionAt P Q X = ⟨ Q X ⟩ → ⟦ P ⟧ ⟨ X ⟩

IsSectionAt :
  (P : Polynomial) (Q : hSet ℓ-zero → hSet ℓ-zero)
  (X : hSet ℓ-zero) →
  (q : ⟦ P ⟧ ⟨ X ⟩ → ⟨ Q X ⟩) →
  SectionAt P Q X → Type
IsSectionAt P Q X q c = (u : ⟨ Q X ⟩) → q (c u) ≡ u

AlgebraAt :
  Signature → (hSet ℓ-zero → hSet ℓ-zero) → hSet ℓ-zero → Type
AlgebraAt Σ Q X =
  (o : Op Σ) →
  (Fin (arity Σ o) → ⟨ Q X ⟩) → ⟨ Q X ⟩

AlgebraStructure :
  Signature → (hSet ℓ-zero → hSet ℓ-zero) → Type
AlgebraStructure Σ Q = (X : hSet ℓ-zero) → AlgebraAt Σ Q X
