{-# OPTIONS --prop #-}
module Cubical.Prop.DecProp where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base
open import Cubical.Prop.Bottom
open import Cubical.Prop.Top

module _ {ℓ}{X : Type ℓ} where
  Dec→Prop : Dec X → Prop
  Dec→Prop (yes p) = ⊤
  Dec→Prop (no ¬p) = ⊥

  Dec→Prop→X : (d : Dec X) → Dec→Prop d → X
  Dec→Prop→X (yes p) _ = p
