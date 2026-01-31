module Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
  where

open import Cubical.Foundations.Prelude

private variable ℓ ℓ' : Level

module _ (ob : Type ℓ) where
  data ProdExpr : Type ℓ where
    ↑_ : ob → ProdExpr
    _×_ : ProdExpr → ProdExpr → ProdExpr
    ⊤ : ProdExpr
  record ProductQuiver ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      mor : Type ℓ'
      dom : mor → ProdExpr
      cod : mor → ProdExpr

record ×Quiver ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    ob : Type ℓ
    Q : ProductQuiver ob ℓ'
  open ProductQuiver Q public
  Expr : Type ℓ
  Expr = ProdExpr ob
