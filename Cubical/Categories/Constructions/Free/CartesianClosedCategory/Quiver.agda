{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Constructions.Free.CartesianClosedCategory.Quiver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Quiver.Base

private variable ℓ ℓ' : Level

module _ (ob : Type ℓ) where
  data CCCExpr : Type ℓ where
    ↑_ : ob → CCCExpr
    _×_ : CCCExpr → CCCExpr → CCCExpr
    ⊤ : CCCExpr
    _⇒_ : CCCExpr → CCCExpr → CCCExpr

record ×⇒Quiver ℓ ℓ' : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  field
    ob : Type ℓ
    Q : QuiverOver (CCCExpr ob) ℓ'
  open QuiverOver Q public
  obExpr : Type ℓ
  obExpr = CCCExpr ob
  open CCCExpr obExpr public

Quiver→×⇒Quiver : ∀{ℓ ℓ' : Level} → Quiver ℓ ℓ' → ×⇒Quiver ℓ ℓ'
Quiver→×⇒Quiver Q .×⇒Quiver.ob = Q .fst
Quiver→×⇒Quiver Q .×⇒Quiver.Q .QuiverOver.mor = Q .snd .QuiverOver.mor
Quiver→×⇒Quiver Q .×⇒Quiver.Q .QuiverOver.dom = ↑_ ∘S Q .snd .QuiverOver.dom
Quiver→×⇒Quiver Q .×⇒Quiver.Q .QuiverOver.cod = ↑_ ∘S Q .snd .QuiverOver.cod
