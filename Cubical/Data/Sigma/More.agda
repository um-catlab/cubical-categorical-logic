module Cubical.Data.Sigma.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

open import Cubical.Data.Prod using (_×ω_; _,_)
open import Cubical.Data.Sigma

open Iso
open _×ω_

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : (a : A) → Type ℓ
    C : (a : A) (b : B a) → Type ℓ

change-contractum : (p : ∃![ x₀ ∈ A ] B x₀) → singl (p .fst .fst)
                  → ∃![ x ∈ A ] B x
change-contractum {B = B} ((x₀ , p₀) , contr) (x , x₀≡x) =
  (x , subst B x₀≡x p₀)
  , (λ yq → ΣPathP ((sym x₀≡x) , symP (subst-filler B x₀≡x p₀)) ∙ contr yq)

FrobeniusReciprocity :
  ∀ (f : A → A') y
  → Iso (Σ[ (x , _) ∈ fiber f y ] (B x) × B' (f x))
        ((Σ[ (x , _) ∈ fiber f y ] B x) × B' y)
FrobeniusReciprocity {B' = B'} f y .fun ((x , fx≡y) , p , q) =
  ((x , fx≡y) , p) , subst B' fx≡y q
FrobeniusReciprocity {B' = B'} f y .inv (((x , fx≡y) , p) , q) =
  (x , fx≡y) , (p , subst B' (sym $ fx≡y) q)
FrobeniusReciprocity {B' = B'} f y .rightInv (((x , fx≡y) , p) , q) =
  ΣPathP (refl , (substSubst⁻ B' fx≡y q))
FrobeniusReciprocity {B' = B'} f y .leftInv ((x , fx≡y) , p , q) =
  ΣPathP (refl , (ΣPathP (refl , (substSubst⁻ B' (sym $ fx≡y) q))))

record Σω (A : Typeω) (B : A → Typeω) : Typeω where
  constructor _,_
  field
    fst : A
    snd : B fst

Σω-syntax : ∀ (A : Typeω) (B : A → Typeω) → Typeω
Σω-syntax = Σω

syntax Σω-syntax A (λ x → B) = Σω[ x ∈ A ] B

open Σω

record Liftω (A : Type ℓ) : Typeω where
  constructor liftω
  field
    lowerω : A

open Liftω

mapω : {A : Type ℓ}{B : Type ℓ'} → (A → B) → Liftω A → Liftω B
mapω f a = liftω (f (a .lowerω))

mapω' : {A : Type ℓ}{β : A → Level} (f : (a : A) → Type (β a)) (a : Liftω A) → Typeω
mapω' f a = Liftω (f (a .lowerω))

