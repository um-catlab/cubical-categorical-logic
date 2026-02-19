module Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Quiver.Base

private variable ℓ ℓ' : Level

module _ (ob : Type ℓ) where
  data ProdExpr : Type ℓ where
    ↑_ : ob → ProdExpr
    _×_ : ProdExpr → ProdExpr → ProdExpr
    ⊤ : ProdExpr
record ×Quiver ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    ob : Type ℓ
    Q : QuiverOver (ProdExpr ob) ℓ'
  open QuiverOver Q public
  Expr : Type ℓ
  Expr = ProdExpr ob
  open ProdExpr Expr public

Quiver→×Quiver : ∀{ℓ ℓ' : Level} → Quiver ℓ ℓ' → ×Quiver ℓ ℓ'
Quiver→×Quiver Q .×Quiver.ob = Q .fst
Quiver→×Quiver Q .×Quiver.Q .QuiverOver.mor = Q .snd .QuiverOver.mor
Quiver→×Quiver Q .×Quiver.Q .QuiverOver.dom = ↑_ ∘S Q .snd .QuiverOver.dom
Quiver→×Quiver Q .×Quiver.Q .QuiverOver.cod = ↑_ ∘S Q .snd .QuiverOver.cod
