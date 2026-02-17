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

-- open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
-- open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓS ℓR : Level

open Category
open Functor
open NatTrans
open NatIso
open PshHom
open PshIso
open UniversalElement
module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         (P : Profunctor C D ℓS)
         (ues : UniversalElements P)
         where
  open UniversalElementNotation

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
  FunctorComprehension-Repr :
    RelatorIso
    (CurriedToBifunctorL P)
    (compR (HomBif D) FunctorComprehension)
  FunctorComprehension-Repr .trans = mkRelatorHom (λ d c → intro (ues c))
    (λ d d' c f p → sym $ intro-natural (ues c))
    λ d c c' p g → intro≡ (ues c') $ sym $
      ((intro (ues c) p D.⋆ intro (ues c') (ues c .element P.⋆ʳᶜ g)) P.⋆ᶜʳ ues c' .element)
        ≡⟨ P.⋆Assocᶜᶜʳ _ _ _ ∙ P.⟨ refl ⟩⋆ᶜʳ⟨ β (ues c') ⟩ ⟩
      (intro (ues c) p P.⋆ᶜʳ (ues c .element P.⋆ʳᶜ g))
        ≡⟨ sym (P.⋆Assocᶜʳᶜ _ _ _) ∙ P.⟨ β $ ues c ⟩⋆ʳᶜ⟨ refl ⟩ ⟩
      (p P.⋆ʳᶜ g)
        ∎
  FunctorComprehension-Repr .nIso (d , c) .fst = P._⋆ᶜʳ ues c .element
  FunctorComprehension-Repr .nIso (d , c) .snd .fst f = sym $ η $ ues c
  FunctorComprehension-Repr .nIso (d , c) .snd .snd p = β $ ues c

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} (F G : Functor C D)
  where
  -- TODO: This should probably go in something like Profunctor.Representable. In fact maybe this whole file should be moved to Profunctor.Representable.
  -- TODO: Can this be rewritten to use one of the many Yonedas we already have?
  Functorial-Yo : (αYo : (RelatorHom (compR (HomBif D) F) (compR (HomBif D) G))) → NatTrans F G
  Functorial-Yo αYo .N-ob x = αYo .N-ob (F ⟅ x ⟆ , x) (D .id)
  Functorial-Yo αYo .N-hom f =
    sym (natL αYo (F ⟪ f ⟫) (D .id))
    ∙ cong (αYo .N-ob _) (idTrans F .N-hom f)
    ∙ natR αYo (id D) f

  Functorial-Yo-Iso :
    (αYo : (RelatorIso (compR (HomBif D) F) (compR (HomBif D) G)))
    → NatIso F G
  Functorial-Yo-Iso αYo .trans = Functorial-Yo (αYo .trans)
  Functorial-Yo-Iso αYo .nIso x .isIso.inv = αYo .nIso (G .F-ob x , x) .fst (id D)
  Functorial-Yo-Iso αYo .nIso x .isIso.sec = sym (natL (αYo .trans) _ _)
    ∙ cong (αYo .trans .N-ob _) (D .⋆IdR _)
    ∙ αYo .nIso (G .F-ob x , x) .snd .fst (id D)
  Functorial-Yo-Iso αYo .nIso x .isIso.ret =
    sym (natL (invPshIso αYo .trans) _ _)
    ∙ cong (αYo .nIso _ .fst) (D .⋆IdR _)
    ∙ αYo .nIso (F .F-ob x , x) .snd .snd (id D)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
         (P : Profunctor C D ℓS)(Q : Profunctor C E ℓR)
         (F : Functor D E)
         (α : ProfunctorHom P (reindPshF F ∘F Q))
         (uesP : UniversalElements P)
         where

  preserves-UE→NatIso
    : (uesQ : UniversalElements Q)
    → (F-pres-uesP : ∀ (x : C .ob) → preservesUniversalElement (app-ProfHom α x) (uesP x))
    → NatIso (F ∘F FunctorComprehension P uesP) (FunctorComprehension Q uesQ)
  preserves-UE→NatIso uesQ F-pres-uesP = isosToNatIso
    (λ x → UniversalElement→Iso (record { vertex = _ ; element = α .N-ob _ (uesP x .element) ; universal = F-pres-uesP x }
      ◁PshIso invPshIso uesQ.asPshIso))
    λ x y f →
      (F ⟪ uesP.intro (uesP.element P.⋆ʳᶜ f) ⟫ E.⋆ uesQ.intro F-uesP.element)
        ≡⟨ uesQ.intro-natural ∙ uesQ.intro≡
          (((F ⟪ uesP.intro (uesP.element P.⋆ʳᶜ f) ⟫) Q.⋆ᶜʳ F-uesP.element)
            ≡⟨ sym (natL α _ _) ∙ cong (α .N-ob _) uesP.β ∙ natR α _ _ ⟩
          (F-uesP.element Q.⋆ʳᶜ f)
            ≡⟨ Q.⟨ sym $ uesQ.β ⟩⋆ʳᶜ⟨ refl ⟩ ∙ Q.⋆Assocᶜʳᶜ _ _ _ ⟩
          (uesQ.intro F-uesP.element Q.⋆ᶜʳ (uesQ.element Q.⋆ʳᶜ f))
            ≡⟨ Q.⟨ refl ⟩⋆ᶜʳ⟨ (sym $ uesQ.β) ⟩ ∙ (sym $ Q.⋆Assocᶜᶜʳ _ _ _) ⟩
          ((uesQ.intro F-uesP.element E.⋆ uesQ.intro (uesQ.element Q.⋆ʳᶜ f)) Q.⋆ᶜʳ uesQ.element) ∎) ⟩
      (uesQ.intro F-uesP.element E.⋆ uesQ.intro (uesQ.element Q.⋆ʳᶜ f))
        ∎
    where
      module E = Category E
      module P = ProfunctorNotation P
      module Q = ProfunctorNotation Q
      F-uesP : ∀ x → UniversalElement E (Q ⟅ x ⟆)
      F-uesP = λ x → record { vertex = F-ob F (uesP x .vertex) ; element = app-ProfHom α x .N-ob (uesP x .vertex) (uesP x .element) ; universal = F-pres-uesP x }
      module uesQ {x} = UniversalElementNotation (uesQ x)
      module F-uesP {x} = UniversalElementNotation {P = Q ⟅ x ⟆} (F-uesP x)
      module uesP {x} = UniversalElementNotation (uesP x)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         (P : Profunctor C D ℓS)(Q : Profunctor C D ℓR)
         (uesP : UniversalElements P)
         (uesQ : UniversalElements Q)
         (α : ProfunctorIso P Q)
         where
  FunctorComprehension-NatIso : NatIso (FunctorComprehension P uesP) (FunctorComprehension Q uesQ)
  FunctorComprehension-NatIso =
    Functorial-Yo-Iso (FunctorComprehension P uesP) (FunctorComprehension Q uesQ) $
    (invPshIso $ FunctorComprehension-Repr P uesP)
    ⋆PshIso α
    ⋆PshIso FunctorComprehension-Repr Q uesQ
