{-# OPTIONS --prop #-}
module Cubical.Prop.ToType where

open import Cubical.Foundations.Prelude

record Prop→Type {ℓ} (P : Prop ℓ) : Type ℓ where
  constructor ı
  field
    pf : P

isProp-Prop→Type : ∀ {ℓ}{P : Prop ℓ} → isProp (Prop→Type P)
isProp-Prop→Type x y = refl
