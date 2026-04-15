module Cubical.HITs.MappingCylinder.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

data MappingCylinder {ℓ ℓ'}{A : Type ℓ}{B : Type ℓ'}(f : A → B) : Type (ℓ-max ℓ ℓ') where
  inl : A → MappingCylinder f
  inr : B → MappingCylinder f
  push : (a : A) → inl a ≡ inr (f a)

module _ {ℓ ℓ'}{A : Type ℓ}{B : Type ℓ'}{f : A → B} where
  MappingCylinder→Cod : MappingCylinder f → B
  MappingCylinder→Cod (inl x) = f x
  MappingCylinder→Cod (inr x) = x
  MappingCylinder→Cod (push a i) = f a

  MappingCylinder≃Cod : isIso MappingCylinder→Cod
  MappingCylinder≃Cod .fst = inr
  MappingCylinder≃Cod .snd .fst b = refl
  MappingCylinder≃Cod .snd .snd (inl x) i = push x (~ i)
  MappingCylinder≃Cod .snd .snd (inr x) = refl
  MappingCylinder≃Cod .snd .snd (push a i) j = push a (i ∨ ~ j)
