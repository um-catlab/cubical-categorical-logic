{-# OPTIONS --lossy-unification #-}
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
module Cubical.Categories.FunctorComprehension.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Functor
open NatTrans
open UniversalElement
open UniversalElementNotation

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         (P : Profunctor C D ℓS)
         (ues : UniversalElements P)
         where
  private
    module C = Category C
    module D = Category D
    module P = RelatorNotation (CurriedToBifunctorL P)
  FunctorComprehension : Functor C D
  FunctorComprehension .F-ob x = ues x .vertex
  FunctorComprehension .F-hom {x}{y} f =
    intro (ues y) (ues x .element P.⋆ʳᶜ f)
  FunctorComprehension .F-id {x} =
    cong (intro (ues x)) (P.⋆IdRʳᶜ (ues x .element))
    ∙ (sym $ weak-η (ues x))
  FunctorComprehension .F-seq {x}{y}{z} f g =
    intro≡ (ues z)
      (sym (P.⋆Assocʳᶜᶜ _ _ _)
      ∙ P.⟨ sym $ β (ues y) ⟩⋆ʳᶜ⟨ refl ⟩
      ∙ P.⋆Assocᶜʳᶜ _ _ _
      ∙ P.⟨ refl ⟩⋆ᶜʳ⟨ sym $ β (ues z) ⟩
      ∙ (sym $ P.⋆Assocᶜᶜʳ _ _ _))

  -- P ≅ Yo ∘F FunctorComprehension P ues
  open PshHom
  open PshIso
  FunctorComprehension-Iso :
    RelatorIso
    (CurriedToBifunctorL P)
    (compR (HomBif D) FunctorComprehension)
  FunctorComprehension-Iso .trans = mkRelatorHom (λ d c → intro (ues c))
    (λ d d' c f p → sym $ intro-natural (ues c))
    λ d c c' p g → intro≡ (ues c') $ sym $
      ((intro (ues c) p D.⋆ intro (ues c') (ues c .element P.⋆ʳᶜ g)) P.⋆ᶜʳ ues c' .element)
        ≡⟨ P.⋆Assocᶜᶜʳ _ _ _ ∙ P.⟨ refl ⟩⋆ᶜʳ⟨ β (ues c') ⟩ ⟩
      (intro (ues c) p P.⋆ᶜʳ (ues c .element P.⋆ʳᶜ g))
        ≡⟨ sym (P.⋆Assocᶜʳᶜ _ _ _) ∙ P.⟨ β $ ues c ⟩⋆ʳᶜ⟨ refl ⟩ ⟩
      (p P.⋆ʳᶜ g)
        ∎
  FunctorComprehension-Iso .nIso (d , c) .fst = P._⋆ᶜʳ ues c .element
  FunctorComprehension-Iso .nIso (d , c) .snd .fst f = sym $ η $ ues c
  FunctorComprehension-Iso .nIso (d , c) .snd .snd p = β $ ues c
