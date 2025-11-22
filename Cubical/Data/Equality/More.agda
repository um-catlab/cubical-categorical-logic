{-# OPTIONS -W noUnsupportedIndexedMatch #-}
module Cubical.Data.Equality.More where

open import Cubical.Foundations.Prelude
  hiding (_≡_ ; step-≡ ; _∎ ; isPropIsContr)
  renaming ( refl      to reflPath
           ; transport to transportPath
           ; J         to JPath
           ; JRefl     to JPathRefl
           ; sym       to symPath
           ; _∙_       to compPath
           ; cong      to congPath
           ; subst     to substPath
           ; substRefl to substPathReflPath
           ; funExt    to funExtPath
           ; isContr   to isContrPath
           ; isProp    to isPropPath
           )
open import Cubical.Foundations.Equiv
  renaming ( fiber     to fiberPath
           ; isEquiv   to isEquivPath
           ; _≃_       to EquivPath
           ; equivFun  to equivFunPath
           ; isPropIsEquiv to isPropIsEquivPath
           )
  hiding   ( equivCtr
           ; equivIsEquiv )
open import Cubical.Foundations.Isomorphism
  using ()
  renaming ( Iso to IsoPath
           ; iso to isoPath
           ; isoToPath to isoPathToPath
           ; isoToEquiv to isoPathToEquivPath
           )
open import Cubical.Data.Equality

private
 variable
  a b c ℓ ℓ' : Level
  A : Type a
  B : Type b
  C : Type c
  x y z : A
  Aω : Typeω
  Aω₁ : Typeω₁

ap₂ : (f : A → B → C) {x y : A} {u v : B} → x ≡ y → u ≡ v →
  f x u ≡ f y v
ap₂ f refl refl = refl

mixedHEq : {A0 A1 : Type ℓ} (Aeq : A0 ≡ A1) (a0 : A0)(a1 : A1) → Type _
mixedHEq Aeq a0 a1 = Path _ (transport (λ A → A) Aeq a0) a1

-- Version of _≡_ where the type is an explicit argument, analogous to Path
Eq : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Eq A a b = a ≡ b

data _≡ω_ {A : Typeω} : A → A → Typeω where
  reflω : {x : A} → x ≡ω x

infix 4 _≡ω_

data _≡ω₁_ {A : Typeω₁} : A → A → Typeω₁ where
  reflω₁ : {x : A} → x ≡ω₁ x

infix 4 _≡ω₁_

-- Symmetry
symω : {A : Typeω} {x y : A} → x ≡ω y → y ≡ω x
symω reflω = reflω

-- Transitivity
transω : {A : Typeω} {x y z : A} → x ≡ω y → y ≡ω z → x ≡ω z
transω reflω q = q

-- Congruence
congω : {A B : Typeω} (f : A → B) {x y : A} → x ≡ω y → f x ≡ω f y
congω f reflω = reflω

congω₁ : {A B : Typeω₁} (f : A → B) {x y : A} → x ≡ω₁ y → f x ≡ω₁ f y
congω₁ f reflω₁ = reflω₁

Jω : {A : Typeω} (P : (x y : A) → x ≡ω y → Typeω)
   → (∀ x → P x x reflω)
   → ∀ {x y} (p : x ≡ω y) → P x y p
Jω P prefl reflω = prefl _

cong₂ω : {A B C : Typeω} (f : A → B → C)
       → {x y : A} → x ≡ω y
       → {u v : B} → u ≡ω v
       → f x u ≡ω f y v
cong₂ω f reflω reflω = reflω

transportω : ∀ (C : Aω → Typeω) {x y : Aω} → x ≡ω y → C x → C y
transportω C reflω b = b

HEqω : {A0 A1 : Typeω}(Aeq : A0 ≡ω₁ A1)(a0 : A0)(a1 : A1) → Typeω
HEqω reflω₁ a0 a1 = a0 ≡ω a1
