{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.General where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category

-- A profunctor, also called a distributor is a generalization of a
-- functor where the values are not objects of the codomain, but
-- instead presheaves
Profunctor : (C : Category ℓC ℓC')(D : Category ℓD ℓD') → ∀ ℓS → Type _
Profunctor C D ℓS = Functor C (PresheafCategory D ℓS)

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') ℓS where
  PROFUNCTOR : Category _ _
  PROFUNCTOR = FUNCTOR C (PresheafCategory D ℓS)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (R : Profunctor C D ℓS) where

  UniversalElements : Type _
  UniversalElements =
    ∀ (c : C .ob)
    → UniversalElement D (R ⟅ c ⟆)
