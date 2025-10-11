{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Profunctor.Homomorphism.Bilinear where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR ℓQ : Level

module _ {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where
  private
    module B = Category B
    module C = Category C
    module D = Category D
    variable
      b b' b'' : B.ob
      c c' c'' : C.ob
      d d' d'' : D.ob

  -- Examples:
  -- 1. Composition is a bilinear map C.Hom C.Hom → C.Hom
  -- 2. Displayed composition in a displayed cat is Cᴰ[ f ] Cᴰ[ g ] → Cᴰ[ f ⋆ g ]
  -- 3. Universal bilinear map Q R → Q ⊙ R
  record Bilinear (Q : Profunctor C B ℓQ)
                  (R : Profunctor D C ℓR)
                  (S : Profunctor D B ℓS)
         : Type (ℓ-max (ℓ-max ℓB ℓB')
                (ℓ-max (ℓ-max ℓC ℓC')
                (ℓ-max (ℓ-max ℓD ℓD')
                (ℓ-max ℓQ (ℓ-max ℓR ℓS))))) where
    private
      module Q = ProfunctorNotation Q
      module R = ProfunctorNotation R
      module S = ProfunctorNotation S
    field
      _⋆ᵖ_ : ∀ {b c d} → Q.Het[ b , c ] → R.Het[ c , d ] → S.Het[ b , d ]
      ⋆Assocᶜᵖᵖ : ∀ (f : B.Hom[ b , b' ])(q : Q.Het[ b' , c ])(r : R.Het[ c , d ])
        → ((f Q.⋆ᶜᵖ q) ⋆ᵖ r) ≡ (f S.⋆ᶜᵖ (q ⋆ᵖ r))
      ⋆Assocᵖᶜᵖ : ∀ (q : Q.Het[ b , c ])(g : C.Hom[ c , c' ])(r : R.Het[ c' , d ])
        → ((q Q.⋆ᵖᶜ g) ⋆ᵖ r) ≡ (q ⋆ᵖ (g R.⋆ᶜᵖ r))
      ⋆Assocᵖᵖᶜ : ∀ (q : Q.Het[ b , c ])(r : R.Het[ c , d ])(h : D.Hom[ d , d' ])
        → ((q ⋆ᵖ r) S.⋆ᵖᶜ h) ≡ (q ⋆ᵖ (r R.⋆ᵖᶜ h))
