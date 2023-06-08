{-# OPTIONS --safe #-}

module Cubical.Categories.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Bifunctor hiding (Fst; Snd)
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

private
  variable
    ℓC ℓC' : Level

open Category
open UnivElt
open isUniversal

module _ (C : Category ℓC ℓC') where
  Exponential : (c d : C .ob) → (∀ (e : C .ob) → BinProduct C c e) → Type _
  Exponential c d c×- = RightAdjointAt C C (BinProductWithF _ c×-) d

  module _ (bp : BinProducts C) where
    ExpProf : C o-[ ℓC' ]-* (C ^op ×C C)
    ExpProf = Functor→Bifunctor (HomFunctor C ∘F
      (  (BinProductF C bp ∘F (Fst C (C ×C C ^op) ,F
         Fst C (C ^op) ∘F Snd C (C ×C C ^op)) ^opF)
      ,F Snd (C ^op) C ∘F Snd (C ^op) (C ^op ×C C)))

    Exponentials : Type _
    Exponentials = ParamUnivElt (C ^op ×C C) C ExpProf

    ExponentialF : Exponentials → Functor (C ^op ×C C) C
    ExponentialF exps = ParamUnivElt→ProfRepresentation _ _ _ exps .fst

    module ExpNotation (exp : Exponentials) where
      open Notation C bp

      _⇒_ : C .ob → C .ob → C .ob
      c ⇒ d = exp (c , d) .vertex

      lda : ∀ {Γ c d} → C [ Γ × c , d ] → C [ Γ , c ⇒ d ]
      lda f = exp _ .universal .coinduction f

      app : ∀ {c d} → C [ (c ⇒ d) × c , d ]
      app = exp _ .element

      app' : ∀ {Γ c d} → C [ Γ , c ⇒ d ] → C [ Γ , c ] → C [ Γ , d ]
      app' f x = app ∘⟨ C ⟩ (f ,p x)

      _⇒F_ : ∀ {c c' d d'} (f : C [ c' , c ])(g : C [ d , d' ])
           → C [ c ⇒ d , c' ⇒ d' ]
      f ⇒F g = lda (g ∘⟨ C ⟩ (app' π₁ (f ∘⟨ C ⟩ π₂)))

      -- private
        -- The following should ideally follow by refl but
        -- both definitions have more ids than expected
        -- bad : ∀ {c c' d d'} (f : C [ c' , c ])(g : C [ d , d' ])
        --     → f ⇒F g ≡ ExponentialF exp ⟪ f , g ⟫
        -- bad f g = {!refl!}
