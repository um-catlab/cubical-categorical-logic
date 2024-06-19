{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
  where

open import Cubical.Foundations.Prelude

private variable ℓ ℓ' : Level

module _ (ob : Type ℓ) where
  data ProdExpr : Type ℓ where
    ↑_ : ob → ProdExpr
    _×_ : ProdExpr → ProdExpr → ProdExpr
    ⊤ : ProdExpr
  record ProductQuiver : Type (ℓ-suc ℓ) where
    field
      mor : Type ℓ
      dom : mor → ProdExpr
      cod : mor → ProdExpr

×Quiver : ∀ ℓ → Type (ℓ-suc ℓ)
×Quiver ℓ = Σ[ ob ∈ Type ℓ ] ProductQuiver ob

module ×QuiverNotation (Q : ×Quiver ℓ) where
  open ProductQuiver
  Ob = ProdExpr (Q .fst)
  Dom = Q .snd .dom
  Cod = Q .snd .cod
