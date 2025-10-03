module Cubical.Foundations.Isomorphism.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ

open Iso

isoFun≡ : ∀ {x y} → (f : Iso A B) → x ≡ f .inv y → f .fun x ≡ y
isoFun≡ f x≡f⁻y = isoInvInjective f _ _ (f .leftInv _ ∙ x≡f⁻y)

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

-- Version of isoFunInjective for PathPs
fiberwiseIsoFunInjective :
  ∀ {A : Type ℓ}{P : A → Type ℓ'}{Q : A → Type ℓ''}
  {a a' p p'}{a≡a' : a ≡ a'}
  (f : ∀ a → Iso (P a) (Q a))
  → PathP (λ i → Q (a≡a' i)) (Iso.fun (f a) p) (Iso.fun (f a') p')
  → PathP (λ i → P (a≡a' i)) p p'
fiberwiseIsoFunInjective f fp≡fp' =
  (sym $ Iso.leftInv (f _) _)
  ◁ congP (λ _ → f _ .Iso.inv) fp≡fp'
  ▷ Iso.leftInv (f _) _

