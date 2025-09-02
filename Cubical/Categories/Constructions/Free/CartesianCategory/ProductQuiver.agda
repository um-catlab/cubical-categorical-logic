module Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

private variable ℓ ℓ' : Level

module _ (ob : Type ℓ) where
  data ProdExpr : Type ℓ where
    ↑_ : ob → ProdExpr
    _×_ : ProdExpr → ProdExpr → ProdExpr
    ⊤ : ProdExpr
  -- This is the "normal" signature for cartesian theories as first used in eg
  -- Gluing/CartesianCategory or Gluing/Conservativity
  record ProductQuiver ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      mor : Type ℓ'
      dom : mor → ProdExpr
      cod : mor → ProdExpr

  -- This variant notion of cartesian signature is more restrictive in order for
  -- the normal forms of the free theory to be more amenable to a hand crafted
  -- description
  --
  -- atomic function symbols are only at base types, since WLOG a function
  -- symbol at a product type is "just" a finite number of paired function
  -- symbols
  record ProductQuiver' ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      mor : Type ℓ'
      dom : mor → ProdExpr
      cod : mor → ob

  module _ {ℓ'} (Q : ProductQuiver' ℓ') where
    ProductQuiver'→ProductQuiver : ProductQuiver ℓ'
    ProductQuiver'→ProductQuiver .ProductQuiver.mor = Q .ProductQuiver'.mor
    ProductQuiver'→ProductQuiver .ProductQuiver.dom = Q .ProductQuiver'.dom
    ProductQuiver'→ProductQuiver .ProductQuiver.cod = ↑_ ∘S Q .ProductQuiver'.cod

record ×Quiver ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    ob : Type ℓ
    ×Q : ProductQuiver ob ℓ'

record ×Quiver' ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    ob : Type ℓ
    ×Q : ProductQuiver' ob ℓ'

module ×QuiverNotation (Q : ×Quiver ℓ ℓ') where
  open ×Quiver Q using (ob) public
  open ×Quiver Q using (×Q)
  Ob = ProdExpr ob
  open ProductQuiver ×Q public

module ×Quiver'Notation (Q : ×Quiver' ℓ ℓ') where
  open ×Quiver' Q using (ob) public
  open ×Quiver' Q using (×Q)
  Ob = ProdExpr ob
  open ProductQuiver' ×Q public

×Quiver'→×Quiver : ∀{ℓ ℓ'} → ×Quiver' ℓ ℓ' → ×Quiver ℓ ℓ'
×Quiver'→×Quiver Q .×Quiver.ob = Q .×Quiver'.ob
×Quiver'→×Quiver Q .×Quiver.×Q = ProductQuiver'→ProductQuiver
  (Q .×Quiver'.ob) (Q .×Quiver'.×Q)
