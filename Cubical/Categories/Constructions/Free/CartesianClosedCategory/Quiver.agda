{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Constructions.Free.CartesianClosedCategory.Quiver where

open import Cubical.Foundations.Prelude

private variable ℓ ℓ' : Level

module _ (ob : Type ℓ) where
  data Expr : Type ℓ where
    ↑_ : ob → Expr
    _×_ : Expr → Expr → Expr
    ⊤ : Expr
    _⇒_ : Expr → Expr → Expr
  record Quiver ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      mor : Type ℓ'
      dom : mor → Expr
      cod : mor → Expr

×⇒Quiver : ∀ ℓ ℓ' → Type _
×⇒Quiver ℓ ℓ' = Σ[ ob ∈ Type ℓ ] Quiver ob ℓ'

module ×⇒QuiverNotation (Q : ×⇒Quiver ℓ ℓ') where
  open Quiver
  Ob = Expr (Q .fst)
  Dom = Q .snd .dom
  Cod = Q .snd .cod
