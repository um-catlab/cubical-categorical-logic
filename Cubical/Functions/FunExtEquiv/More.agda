module Cubical.Functions.FunExtEquiv.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level

open Iso

-- A fibre of postcomposition is a family of fibres.
fiberPostcompIso : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  (f : B → C) (g : A → C)
  → Iso (fiber (λ (h : A → B) → f ∘ h) g) ((a : A) → fiber f (g a))
fiberPostcompIso f g .fun (h , p) a = h a , funExt⁻ p a
fiberPostcompIso f g .inv k = (λ a → k a .fst) , funExt λ a → k a .snd
fiberPostcompIso f g .sec k = refl
fiberPostcompIso f g .ret hp = refl
