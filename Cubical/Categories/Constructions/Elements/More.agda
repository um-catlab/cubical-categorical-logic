{-# OPTIONS --safe #-}

-- The Category of Elements

open import Cubical.Categories.Category

module Cubical.Categories.Constructions.Elements.More where

open import Cubical.Categories.Instances.Sets
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Constructions.Elements

import Cubical.Categories.Morphism as Morphism
import Cubical.Categories.Constructions.Slice as Slice

open Category
open Functor

module _ {ℓ ℓ'} {C : Category ℓ ℓ'} {ℓS} (F : Functor (C ^op) (SET ℓS)) where
  open Contravariant {C = C}
  Elementᴾ : Type (ℓ-max ℓ ℓS)
  Elementᴾ = (∫ᴾ F) .ob

  ∫ᴾhomEqSimpl : ∀ {o1 o2} (f g : (∫ᴾ F) [ o1 , o2 ])
               → fst f ≡ fst g → f ≡ g
  ∫ᴾhomEqSimpl f g p = ∫ᴾhomEq {F = F} f g refl refl p

  domain : Functor (∫ᴾ F) C
  domain .F-ob (x , ϕ) = x
  domain .F-hom (f , comm) = f
  domain .F-id = refl
  domain .F-seq f g = refl
