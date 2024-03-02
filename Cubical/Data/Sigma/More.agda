{-

-}
{-# OPTIONS --safe #-}
module Cubical.Data.Sigma.More where

open import Cubical.Data.Sigma.Base

open import Cubical.Core.Everything

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
