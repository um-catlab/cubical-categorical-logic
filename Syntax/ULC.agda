module Syntax.ULC where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.W.Indexed
open import Cubical.Functions.FunExtEquiv

record Sig ℓ : Type (ℓ-suc ℓ) where
  field
    fun-symbol : Type ℓ
    arity : fun-symbol → ℕ
    isSetFunSymbol : isSet fun-symbol
open Sig
Var = Fin

data Tm {ℓ}(Σ : Sig ℓ)(Γ : ℕ) : Type ℓ where
  var : Var Γ → Tm Σ Γ
  app : (f : Σ .fun-symbol)
      → (Var (Σ .arity f) → Tm Σ Γ)
      → Tm Σ Γ

module isSetTmProof {ℓ} (Σ : Sig ℓ) (Γ : ℕ) where
  Tm-X : Type
  Tm-X = Unit
  Tm-S : Unit → Type ℓ
  Tm-S _ = Var Γ ⊎ (Σ .fun-symbol)
  Tm-P : ∀ (u : Unit) → Tm-S u → Type
  Tm-P u (inl x) = ⊥
  Tm-P u (inr f) = Var (Σ .arity f)

  Tm-inX : ∀ x (s : Tm-S x) → Tm-P x s → Tm-X
  Tm-inX u s p = tt

  Tm→W : Tm Σ Γ → IW Tm-S Tm-P Tm-inX tt
  Tm→W (var x) = node (inl x) (λ ())
  Tm→W (app f args) = node (inr f) (λ p → Tm→W (args p))

  W→Tm : IW Tm-S Tm-P Tm-inX tt → Tm Σ Γ
  W→Tm (node (inl x) subtree) = var x
  W→Tm (node (inr f) subtree) = app f (λ x → W→Tm (subtree x))

  TmRetractOfW : (M : Tm Σ Γ) → W→Tm (Tm→W M) ≡ M
  TmRetractOfW (var x) = refl
  TmRetractOfW (app f args) = cong (app f) (funExt λ x → TmRetractOfW (args x))

  isSetTm-S : isSet (Tm-S tt)
  isSetTm-S = isSet⊎ isSetFin (Σ .isSetFunSymbol)


  isSetTm : isSet (Tm Σ Γ)
  isSetTm =
    isSetRetract Tm→W W→Tm TmRetractOfW
      (isOfHLevelSuc-IW 1 (λ u → isSetTm-S) tt)
