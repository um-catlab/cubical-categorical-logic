module Cubical.Foundations.Isomorphism.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

open Iso

idIsIso : isIso {A = A} λ x → x
idIsIso = IsoToIsIso idIso

isoFun≡ : ∀ {x y} → (f : Iso A B) → x ≡ f .inv y → f .fun x ≡ y
isoFun≡ f x≡f⁻y = isoInvInjective f _ _ (f .ret _ ∙ x≡f⁻y)

isoInv≡ : ∀ {x y} → (f : Iso A B) → x ≡ f .fun y → f .inv x ≡ y
isoInv≡ f = isoFun≡ (invIso f)

isEquivToIsIso : ∀ (f : A → B) → isEquiv f → isIso f
isEquivToIsIso f eq = IsoToIsIso (equivToIso (f , eq))

isPropIsIsoSet :
  ∀ {f : A → B} → isSet A → isSet B → isProp (isIso f)
isPropIsIsoSet {f} isSetA isSetB f⁻ f⁻' =
  Σ≡Prop (λ _ → isProp× (isPropΠ λ _ → isSetB _ _) (isPropΠ λ _ → isSetA _ _))
    (funExt (λ b → isoFunInjective (isIsoToIso f⁻) _ _
      (f⁻ .snd .fst b ∙ sym (f⁻' .snd .fst b))))

section+surjection→Iso : (f : A → B) (g : B → A)
  → section f g → (∀ a → fiber g a) → Iso A B
section+surjection→Iso f g sec surj .fun = f
section+surjection→Iso f g sec surj .inv = g
section+surjection→Iso f g sec surj .sec = sec
section+surjection→Iso f g sec surj .ret a =
  cong g (cong f (sym p) ∙ sec m) ∙ p
  where m = surj a .fst ; p = surj a .snd

