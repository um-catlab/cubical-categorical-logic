{-# OPTIONS --safe #-}
module Cubical.Categories.Yoneda.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Function renaming (_∘_ to _◍_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Presheaf.Base

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Yoneda

private
  variable
    ℓ ℓ' ℓ'' : Level

-- THE YONEDA LEMMA

open NatTrans
open NatTransP
open Functor
open Iso

-- But this one is nice because its action on functors is
-- *definitionally* equal to the definition used in
-- the formulation of the Yoneda lemma
open Category
YONEDA : {C : Category ℓ ℓ'} → Functor C (FUNCTOR (C ^op) (SET ℓ'))
YONEDA {C = C} .F-ob a = C [-, a ]
YONEDA {C = C} .F-hom f .N-ob b g  = g ⋆⟨ C ⟩ f
YONEDA {C = C} .F-hom f .N-hom g = funExt (λ h → C .⋆Assoc g h f)
YONEDA {C = C} .F-id =
  makeNatTransPath (funExt (λ a → funExt (λ f → C .⋆IdR f)))
YONEDA {C = C} .F-seq f g =
  makeNatTransPath (funExt (λ a → funExt (λ h → sym (C .⋆Assoc h f g))))

isFaithfulYoneda : {C : Category ℓ ℓ'} → isFaithful (YONEDA {C = C})
isFaithfulYoneda {C = C} A B f g p =
  sym (C .⋆IdL f) ∙ (λ i → p i .N-ob A (C .id)) ∙ C .⋆IdL g
-- Should prove (in another module) YONEDA ≡ λFl (C ^op) (SET _) (HomFunctor C)
