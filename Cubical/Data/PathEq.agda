module Cubical.HITs.PathEq where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure

data PathEq {X : Type ℓ} (x : X) : X → Type ℓ where
  path : ∀ {x'} → x ≡ x' → PathEq x x'
  eq   : PathEq x x
  eq≡path : eq ≡ path refl
  isPropPathEq : ∀ {x'} → isProp (PathEq x x')

PathEq→Path : ∀ {X : Type ℓ} {x x'} (isSetX : isSet X) (p : PathEq x x') → Path X x x'
PathEq→Path {ℓ} {X} {x} {x'} isSetX (path p) = p
PathEq→Path {ℓ} {X} {x} {x'} isSetX eq = refl
PathEq→Path {ℓ} {X} {x} {x'} isSetX (eq≡path i) = refl
PathEq→Path {ℓ} {X} {x} {x'} isSetX (isPropPathEq p q i) =
  isSetX x x' (PathEq→Path isSetX p) (PathEq→Path isSetX q) i
