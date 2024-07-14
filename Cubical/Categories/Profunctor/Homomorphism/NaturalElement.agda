{-
  A natural element of an endo-relator R : C o-* C
  is a "section": ∀ c. R c c that is "natural" in c.

  This is a kind of "nullary" homomorphism of relators.
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.Homomorphism.NaturalElement where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Profunctor.Relator

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR ℓQ : Level

open Category
module _ {C : Category ℓC ℓC'}
         {R : C o-[ ℓR ]-* C} where
  record NaturalElement : Type (ℓ-max (ℓ-max ℓC ℓC') ℓR) where
    field
      N-ob : (x : C .ob) → R [ x , x ]R
      N-nat : ∀ {x y} (f : C [ x , y ])
            → (f ⋆l⟨ R ⟩ N-ob y) ≡ (N-ob x ⋆r⟨ R ⟩ f)

