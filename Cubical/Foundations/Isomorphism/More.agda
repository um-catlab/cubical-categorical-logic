{-# OPTIONS --safe #-}
module Cubical.Foundations.Isomorphism.More where

open import Cubical.Core.Glue

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

open Iso

isoFun≡ : ∀ {x y} → (f : Iso A B) → x ≡ f .inv y → f .fun x ≡ y
isoFun≡ f x≡f⁻y = isoInvInjective f _ _ (f .leftInv _ ∙ x≡f⁻y)

isoInv≡ : ∀ {x y} → (f : Iso A B) → x ≡ f .fun y → f .inv x ≡ y
isoInv≡ f = isoFun≡ (invIso f)

isEquivToIsIso : ∀ (f : A → B) → isEquiv f → isIso f
isEquivToIsIso f eq = IsoToIsIso (equivToIso (f , eq))
