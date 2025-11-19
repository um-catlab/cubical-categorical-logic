module Cubical.Data.Sigma.More where

open import Cubical.Data.Sigma.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma


open Iso

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
