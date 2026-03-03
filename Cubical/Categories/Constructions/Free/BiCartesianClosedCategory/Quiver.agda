{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Constructions.Free.BiCartesianClosedCategory.Quiver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Quiver.Base

private variable ℓ ℓ' : Level

module _ (ob : Type ℓ) where
  data BiCCCExpr : Type ℓ where
    ↑_ : ob → BiCCCExpr
    _×_ _+_ _⇒_ : BiCCCExpr → BiCCCExpr → BiCCCExpr
    ⊥ ⊤ : BiCCCExpr

record +×⇒Quiver ℓ ℓ' : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  field
    ob : Type ℓ
    Q : QuiverOver (BiCCCExpr ob) ℓ'
  open QuiverOver Q public
  obExpr : Type ℓ
  obExpr = BiCCCExpr ob
  open BiCCCExpr obExpr public

Quiver→+×⇒Quiver : ∀{ℓ ℓ' : Level} → Quiver ℓ ℓ' → +×⇒Quiver ℓ ℓ'
Quiver→+×⇒Quiver Q .+×⇒Quiver.ob = Q .fst
Quiver→+×⇒Quiver Q .+×⇒Quiver.Q .QuiverOver.mor = Q .snd .QuiverOver.mor
Quiver→+×⇒Quiver Q .+×⇒Quiver.Q .QuiverOver.dom = ↑_ ∘S Q .snd .QuiverOver.dom
Quiver→+×⇒Quiver Q .+×⇒Quiver.Q .QuiverOver.cod = ↑_ ∘S Q .snd .QuiverOver.cod
