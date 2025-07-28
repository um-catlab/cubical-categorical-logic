{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct.Redundant.Base as Prod
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Adjoint.2Var
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

private
  variable
    ℓC ℓC' : Level

open Category
open isEquiv

module _ (C : Category ℓC ℓC') where
  Exponential : (c d : C .ob) → (∀ (e : C .ob) → BinProduct C c e) → Type _
  Exponential c d c×- = RightAdjointAt (BinProductWithF _ c×-) d

  Exponential' : (c d : C .ob) → (c×- : hasAllBinProductWith C c) → Type _
  Exponential' c d c×- = RightAdjointAt (a×-F C c×-) d

  module ExponentialNotation {c d} c×- (exp : Exponential c d c×-) where
    open UniversalElementNotation exp public
    open ProdsWithNotation C c×- public
    c⇒d : C .ob
    c⇒d = vertex

    app : C [ a× c⇒d , d ]
    app = element

    lda : ∀ {Γ} → C [ a× Γ , d ] → C [ Γ , c⇒d ]
    lda = intro

    -- this is to test we have the expected definition
    β⇒ : ∀ {Γ} → (f : C [ a× Γ , d ])
      → π₁ ,p (π₂ ⋆⟨ C ⟩ lda f) ⋆⟨ C ⟩ app ≡ f
    β⇒ f = β {p = f}

    η⇒ : ∀ {Γ} → (f : C [ Γ , c⇒d ])
      → f ≡ lda ((π₁ ,p (π₂ ⋆⟨ C ⟩ f)) ⋆⟨ C ⟩ app)
    η⇒ f = η {f = f}

  module _ (bp : BinProducts C) where
    open Notation C bp
    Exponentials : Type _
    Exponentials = RightAdjointL ×Bif

    ExponentialF : Exponentials → Functor ((C ^op) ×C C) C
    ExponentialF exps =
      FunctorComprehension (RightAdjointLProf ×Bif) exps ∘F Prod.Sym
    open UniversalElement

    module ExpsNotation (exp : Exponentials) where
      _⇒_ : C .ob → C .ob → C .ob
      c ⇒ d = exp (d , c) .vertex

      app : ∀ {c d} → C [ (c ⇒ d) × c , d ]
      app {c}{d} = exp (d , c) .element

      lda : ∀ {Γ c d} → C [ Γ × c , d ] → C [ Γ , c ⇒ d ]
      lda  f = exp _ .universal _ .equiv-proof f .fst .fst

      app' : ∀ {Γ c d} → C [ Γ , c ⇒ d ] → C [ Γ , c ] → C [ Γ , d ]
      app' f x = app ∘⟨ C ⟩ (f ,p x)

      ExponentialBif : Bifunctor (C ^op) C C
      ExponentialBif = ExponentialF exp ∘Fb ηBif (C ^op) C
      private
        open Bifunctor
        -- Tests that show the exponential bifunctor has the desirable
        -- definitions
        good : ∀ {c c' d d'} (f : C [ c' , c ])(g : C [ d , d' ])
            → lda
                (g ∘⟨ C ⟩ (app' π₁ (f ∘⟨ C ⟩ π₂))) ≡ ExponentialBif ⟪ f , g ⟫×
        good f g = refl

        good-f : ∀ {c c' d} (f : C [ c' , c ])
            → lda (app' π₁ (f ∘⟨ C ⟩ π₂)) ≡ ExponentialBif .Bif-homL f d
        good-f f = refl

        good-g : ∀ {c d d'} (g : C [ d , d' ])
            → lda (g ∘⟨ C ⟩ app) ≡ ExponentialBif .Bif-homR c g
        good-g g = refl
