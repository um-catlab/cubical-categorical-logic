{-# OPTIONS --safe --lossy-unification #-}
{--
 -- Functor Comprehension
 -- ======================
 -- This module provides a method for constructing functors by showing
 -- that they have a universal property.
 --
 -- The idea is that if you wish to define a functor F : C → D via a
 -- universal property (P c), then the functoriality of F comes for
 -- free if the universal property P is given functorially, that is if
 -- P is a functor P : C → Psh D
 --
 -- That is, if you construct for each c a universal element of P c,
 -- then this can be *uniquely* extended to a functorial action on
 -- morphisms, and furthermore you get that the universal elements so
 -- constructed are natural with respect to this functorial action.
 -- We provide this data in this module in two equivalent forms:
 -- 1. A "natural element" ∀ c → P c (F c)
 -- 2. A natural isomorphism (Y ∘ F ≅ P)
 --
 -- The fact is essentially a corollary of the Yoneda lemma, but we
 --
 -- Constructing a functor in this method saves a lot of work in
 -- repeatedly demonstrating functoriality
 --
 --}
module Cubical.Categories.FunctorComprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Functor
open NatTrans
open UniversalElement
open UniversalElementNotation

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         {P : Profunctor C D ℓS}
         (ues : UniversalElements P)
         where
  private
    module C = Category C
  FunctorComprehension : Functor C D
  FunctorComprehension .F-ob x = ues x .vertex
  FunctorComprehension .F-hom {x}{y} f =
    intro (ues y) ((P ⟪ f ⟫) .N-ob _ (ues x .element))
  FunctorComprehension .F-id {x} =
    (λ i → intro (ues x) (P .F-id i .N-ob _ (ues x .element)))
    ∙ (sym $ weak-η (ues x))
  FunctorComprehension .F-seq {x}{y}{z} f g =
    ((λ i → intro (ues z) (P .F-seq f g i .N-ob _ (ues x .element))))
    ∙ (cong (intro (ues z)) $
      ((λ i → P .F-hom g .N-ob _
        (β (ues y) {p = P .F-hom f .N-ob _ (ues x .element)} (~ i))))
      ∙ funExt⁻ (P .F-hom g .N-hom _) _)
    ∙ (sym $ intro-natural (ues z))
