{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Constructions.Free.CartesianClosedCategory.Quiver where

open import Cubical.Foundations.Prelude

private variable ℓ ℓ' : Level

module _ (ob : Type ℓ) where
  data ObExpr : Type ℓ where
    ↑_ : ob → ObExpr
    _×_ : ObExpr → ObExpr → ObExpr
    ⊤ : ObExpr
    _⇒_ : ObExpr → ObExpr → ObExpr
  record Quiver ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      mor : Type ℓ'
      dom : mor → ObExpr
      cod : mor → ObExpr

record ×⇒Quiver ℓ ℓ' : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  field
    ob : Type ℓ
  obExpr : Type ℓ
  obExpr = ObExpr ob

  field
    mor : Type ℓ'
    dom cod :  mor → obExpr
