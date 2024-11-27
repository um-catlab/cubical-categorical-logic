{-# OPTIONS --safe #-}
module Cubical.Foundations.Isomorphism.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    A B C : Type ℓ
    Aᴰ : A → Type ℓ
    Bᴰ : B → Type ℓᴰ

module _ {ℓ ℓ'}{A : Type ℓ}{B : Type ℓ'}
         {f : A → B}{g : B → A}
         {ℓᴰ ℓᴰ'}{Aᴰ : A → Type ℓᴰ}{Bᴰ : B → Type ℓᴰ'}
         (fᴰ : ∀ a → Aᴰ a → Bᴰ (f a))
         (gᴰ : ∀ b → Bᴰ b → Aᴰ (g b))
         where
  sectionᴰ : section f g → Type (ℓ-max ℓ' ℓᴰ')
  sectionᴰ sec = ∀ {b} bᴰ → PathP (λ i → Bᴰ (sec b i)) (fᴰ _ (gᴰ _ bᴰ)) bᴰ

  retractᴰ : retract f g → Type _
  retractᴰ ret = ∀ {a} aᴰ → PathP (λ i → Aᴰ (ret a i)) (gᴰ _ (fᴰ _ aᴰ)) aᴰ

record Isoᴰ {A : Type ℓ}{B : Type ℓ'}
            (f : Iso A B)
            (Aᴰ : A → Type ℓᴰ) (Bᴰ : B → Type ℓᴰ')
            : Type (ℓ-max (ℓ-max ℓ ℓ')(ℓ-max ℓᴰ ℓᴰ'))
  where
  no-eta-equality
  constructor isoᴰ
  open Iso f
  field
    funᴰ : ∀ a → Aᴰ a → Bᴰ (fun a)
    invᴰ : ∀ b → Bᴰ b → Aᴰ (inv b)
    rightInvᴰ : sectionᴰ funᴰ invᴰ rightInv
    leftInvᴰ : retractᴰ funᴰ invᴰ leftInv

open Iso
open Isoᴰ
Isoᴰ→ΣIso : {A : Type ℓ}{B : Type ℓ'}
            (f : Iso A B)
            (Aᴰ : A → Type ℓᴰ) (Bᴰ : B → Type ℓᴰ')
 → Isoᴰ f Aᴰ Bᴰ
 → Iso (Σ A Aᴰ) (Σ B Bᴰ)
Isoᴰ→ΣIso f Aᴰ Bᴰ fᴰ .fun (a , aᴰ) = (f .fun a) , fᴰ .funᴰ a aᴰ
Isoᴰ→ΣIso f Aᴰ Bᴰ fᴰ .inv (b , bᴰ) = (f .inv b) , fᴰ .invᴰ b bᴰ
Isoᴰ→ΣIso f Aᴰ Bᴰ fᴰ .rightInv (b , bᴰ) =
  ΣPathP (f .rightInv b , fᴰ .rightInvᴰ bᴰ)
Isoᴰ→ΣIso f Aᴰ Bᴰ fᴰ .leftInv (a , aᴰ) =
  ΣPathP ((f .leftInv a) , (fᴰ .leftInvᴰ aᴰ))

isIsoᴰ : {f : A → B} → isIso f → (∀ a → Aᴰ a → Bᴰ (f a)) → Type _
isIsoᴰ {Aᴰ = Aᴰ}{Bᴰ = Bᴰ} f-isIso fᴰ =
  Σ[ gᴰ ∈ (∀ b → Bᴰ b → Aᴰ (f-isIso .fst b) ) ]
  sectionᴰ fᴰ gᴰ (f-isIso .snd .fst) ×
  retractᴰ fᴰ gᴰ (f-isIso .snd .snd)

isoToIsIso' : (f : Iso A B) → isIso (f .Iso.fun)
isoToIsIso' f .fst = Iso.inv f
isoToIsIso' f .snd .fst = Iso.rightInv f
isoToIsIso' f .snd .snd = Iso.leftInv f

pointwiseIsoᴰ : {A : Type ℓ}{B : Type ℓ'}
  (f : A → B)
  (Aᴰ : A → Type ℓᴰ) (Bᴰ : B → Type ℓᴰ')
  → Type _
pointwiseIsoᴰ f Aᴰ Bᴰ = ∀ a → Iso (Aᴰ a) (Bᴰ (f a))

Isoᴰ→PointwiseIsoᴰ : {A : Type ℓ}{B : Type ℓ'}
  (f : Iso A B)
  (Aᴰ : A → Type ℓᴰ) (Bᴰ : B → Type ℓᴰ')
  → Isoᴰ f Aᴰ Bᴰ
  → pointwiseIsoᴰ (f .fun) Aᴰ Bᴰ
Isoᴰ→PointwiseIsoᴰ f Aᴰ Bᴰ fIsoᴰ a .fun = fIsoᴰ .funᴰ a
Isoᴰ→PointwiseIsoᴰ f Aᴰ Bᴰ fIsoᴰ a .inv bᴰ =
  subst Aᴰ (leftInv f a) (fIsoᴰ .invᴰ _ bᴰ)
-- Are these provable without assuming isSet (Bᴰ _) ?
Isoᴰ→PointwiseIsoᴰ f Aᴰ Bᴰ fIsoᴰ a .rightInv bᴰ = {!fIsoᴰ .rightInvᴰ!}
Isoᴰ→PointwiseIsoᴰ f Aᴰ Bᴰ fIsoᴰ a .leftInv aᴰ =
  fromPathP {A = λ i → Aᴰ (leftInv f a i)} (fIsoᴰ .leftInvᴰ aᴰ)

pointwiseIsoᴰ→Isoᴰ : {A : Type ℓ}{B : Type ℓ'}
  (f : Iso A B)
  (Aᴰ : A → Type ℓᴰ) (Bᴰ : B → Type ℓᴰ')
  → pointwiseIsoᴰ (f .fun) Aᴰ Bᴰ
  → Isoᴰ f Aᴰ Bᴰ
pointwiseIsoᴰ→Isoᴰ f Aᴰ Bᴰ fᴰ .funᴰ a = fᴰ a .fun
pointwiseIsoᴰ→Isoᴰ f Aᴰ Bᴰ fᴰ .invᴰ b bᴰ =
  fᴰ (f .inv b) .inv (subst Bᴰ (sym (f .rightInv _)) bᴰ)
pointwiseIsoᴰ→Isoᴰ f Aᴰ Bᴰ fᴰ .rightInvᴰ bᴰ =
  fᴰ _ .rightInv (subst Bᴰ ((sym (f .rightInv _))) bᴰ)
  ◁ symP (subst-filler Bᴰ (sym (f .rightInv _)) bᴰ)
-- Provable without assuming isSet (Aᴰ _) ?
pointwiseIsoᴰ→Isoᴰ f Aᴰ Bᴰ fᴰ .leftInvᴰ aᴰ = {!!}

isEquivToIsIso : {f : A → B} → isEquiv f → isIso f
isEquivToIsIso fEquiv = isoToIsIso' (equivToIso (_ , fEquiv))

isEquivᴰ : {f : A → B} → isEquiv f → (∀ a → Aᴰ a → Bᴰ (f a)) → Type _
isEquivᴰ fEquiv fᴰ = ∀ a → isEquiv (fᴰ a)
