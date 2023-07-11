{-# OPTIONS --safe #-}

module Cubical.Categories.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct.Redundant.Base
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Adjoint.2Var
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

private
  variable
    ℓC ℓC' : Level

open Category
open UniversalElement
open isEquiv

module _ (C : Category ℓC ℓC') where
  Exponential : (c d : C .ob) → (∀ (e : C .ob) → BinProduct C c e) → Type _
  Exponential c d c×- = RightAdjointAt C C (BinProductWithF _ c×-) d

  module _ (bp : BinProducts C) where
    open Notation C bp
    Exponentials : Type _
    Exponentials = 2VarRightAdjointL C C C ×Bif

    ExponentialF : Exponentials → Functor ((C ^op) ×C C) C
    ExponentialF exps = FunctorComprehension _ _ _ exps .fst

    module ExpNotation (exp : Exponentials) where
      _⇒_ : C .ob → C .ob → C .ob
      c ⇒ d = exp (c , d) .vertex

      lda : ∀ {Γ c d} → C [ Γ × c , d ] → C [ Γ , c ⇒ d ]
      lda f = exp _ .universal _ .equiv-proof f .fst .fst

      app : ∀ {c d} → C [ (c ⇒ d) × c , d ]
      app = exp _ .element

      app' : ∀ {Γ c d} → C [ Γ , c ⇒ d ] → C [ Γ , c ] → C [ Γ , d ]
      app' f x = app ∘⟨ C ⟩ (f ,p x)

      ExponentialBif : Bifunctor (C ^op) C C
      ExponentialBif = ExponentialF exp ∘Fb ηBif (C ^op) C
      private
        open Bifunctor
        -- Tests that show the exponential bifunctor has the desirable
        -- definitions
        good : ∀ {c c' d d'} (f : C [ c' , c ])(g : C [ d , d' ])
            → lda (g ∘⟨ C ⟩ (app' π₁ (f ∘⟨ C ⟩ π₂))) ≡ ExponentialBif ⟪ f , g ⟫×
        good f g = refl

        good-f : ∀ {c c' d} (f : C [ c' , c ])
            → lda (app' π₁ (f ∘⟨ C ⟩ π₂)) ≡ ExponentialBif .Bif-homL f d
        good-f f = refl

        good-g : ∀ {c d d'} (g : C [ d , d' ])
            → lda (g ∘⟨ C ⟩ app) ≡ ExponentialBif .Bif-homR c g
        good-g g = refl
