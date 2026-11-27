module Cubical.HITs.MappingCylinder.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
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

  isOfHLevelMappingCylinder : ∀ n → isOfHLevel n B → isOfHLevel n (MappingCylinder f)
  isOfHLevelMappingCylinder n = isOfHLevelRetract n MappingCylinder→Cod inr (MappingCylinder≃Cod .snd .snd)

  elim : ∀ {ℓ''}{M : MappingCylinder f → Type ℓ''}
    → (gA : (a : A) → M (inl a))
    → (gB : (b : B) → M (inr b))
    → (gBf≡gA : ∀ a → PathP (λ i → M (push a i)) (gA a) (gB (f a)))
    → ∀ m → M m
  elim gA gB gBf≡gA (inl x) = gA x
  elim gA gB gBf≡gA (inr x) = gB x
  elim gA gB gBf≡gA (push a i) = gBf≡gA a i

  elimProp : ∀ {ℓ''}{M : MappingCylinder f → Type ℓ''}
    → (∀ m → isProp (M m))
    → (gA : (a : A) → M (inl a))
    → (gB : (b : B) → M (inr b))
    → ∀ m → M m
  elimProp isPropM gA gB = elim gA gB (λ a → isProp→PathP (λ i → isPropM (push a i)) (gA a) (gB (f a)))
