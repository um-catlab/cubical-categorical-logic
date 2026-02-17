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
           ; isSet    to isSetPath
           )
-- open import Cubical.Foundations.Equiv
  renaming ( fiber     to fiberPath
           ; isEquiv   to isEquivPath
           ; _≃_       to EquivPath
           ; equivFun  to equivFunPath
           ; isPropIsEquiv to isPropIsEquivPath
           )
  hiding   ( equivCtr
           ; equivIsEquiv )
-- open import Cubical.Foundations.Isomorphism
  using ()
  renaming ( Iso to IsoPath
           ; iso to isoPath
           ; isoToPath to isoPathToPath
           ; isoToEquiv to isoPathToEquivPath
           )
open import Cubical.Data.Equality
open import Cubical.Data.Sigma hiding (_≡_; ≡-×)

private
 variable
  a b c ℓ ℓ' : Level
  A : Type a
  B : Type b
  C : Type c
  x y z : A

mixedHEq : {A0 A1 : Type ℓ} (Aeq : A0 ≡ A1) (a0 : A0)(a1 : A1) → Type _
mixedHEq Aeq a0 a1 = Path _ (transport (λ A → A) Aeq a0) a1

-- Version of _≡_ where the type is an explicit argument, analogous to Path
Eq : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Eq A a b = a ≡ b

isSet→isSetEq : isSetPath A → {a a' : A} → isPropPath (a ≡ a')
isSet→isSetEq isSetA {a = a} {a' = a'} =
  substPath isPropPath PathPathEq (isSetA a a')

ap₂ : (f : A → B → C) {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
ap₂ f refl refl = refl

J₂ : ∀ {a a' : A} {b b' : B} →
  (M : (a' : A) (b' : B) (p : a ≡ a') (q : b ≡ b') → Type ℓ) →
  M a b refl refl → (p : a ≡ a') → (q : b ≡ b') → M a' b' p q
J₂ M m refl refl = m

≡-× : {A : Type ℓ}{B : Type ℓ'}{ab ab' : A × B}
  → ab .fst ≡ ab' .fst
  → ab .snd ≡ ab' .snd
  → ab ≡ ab'
≡-× refl refl = refl
