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
module Cubical.Categories.Profunctor.FunctorComprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Constructions.Comma
open import Cubical.Categories.Displayed.Constructions.Graph
open import Cubical.Categories.Displayed.Constructions.Weaken.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.HLevels.More
open import Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryL
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Constructions.TotalCategory.More as TotalCat
open import Cubical.Categories.Displayed.Constructions.TotalCategory
  as TotalCatᴰ
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Functor
open UniversalElement
open NatIso
open NatTrans
open isEquiv

module _ (D : Category ℓD ℓD') (ℓS : Level) where
  private
    𝓟 = PresheafCategory D ℓS
    𝓟' = PresheafCategory D (ℓ-max ℓS ℓD')

    -- This should probably be in Yoneda.agda
    LiftPsh = (postcomposeF (D ^op) (LiftF {ℓS}{ℓD'}))
    YO* = (postcomposeF (D ^op) (LiftF {ℓD'}{ℓS}) ∘F YO)

    isFullyFaithfulYO* : isFullyFaithful YO*
    isFullyFaithfulYO* = isFullyFaithfulG∘F
      {G = postcomposeF (D ^op) (LiftF {ℓD'}{ℓS})}
      isFullyFaithfulYO
      (isFullyFaithfulPostcomposeF isFullyFaithfulLiftF)

    Elt : Categoryᴰ (D ×C 𝓟) _ _
    Elt = Graph (Profunctor→Relatoro* Id)

    UElt : Categoryᴰ (D ×C 𝓟) _ _
    UElt = ∫Cᴰ Elt (PropertyOver _ λ ((d , p), e) → isUniversal D p d e)

    module UElt = Categoryᴰ UElt

    HasUniversalElt : Categoryᴰ 𝓟 _ _
    HasUniversalElt = PropertyOver 𝓟 (UniversalElement D)

    WithUniversalElt = ∫Cᴰsl UElt

    hasContrHomsWUE : hasContrHoms WithUniversalElt
    hasContrHomsWUE {P}{Q} α ueP ueQ =
      uniqueExists
        (ueQ.intro ((α ⟦ _ ⟧) ueP.element))
        (ueQ.β , tt)
        (λ _ → isProp× (Q .F-ob _ .snd _ _) isPropUnit)
        λ f (f◃α , tt) → sym (ueQ.η ∙ cong ueQ.intro f◃α)
      where
        ueP' : UniversalElement _ P
        ueP' = record
          { vertex = ueP .fst
          ; element = ueP .snd .fst
          ; universal = ueP .snd .snd
          }
        module ueP = UniversalElementNotation ueP'
        ueQ' : UniversalElement _ Q
        ueQ' = record
          { vertex = ueQ .fst
          ; element = ueQ .snd .fst
          ; universal = ueQ .snd .snd
          }
        module ueQ = UniversalElementNotation ueQ'

    Representation' : Categoryᴰ 𝓟 _ _
    Representation' = IsoCommaᴰ₂ YO* LiftPsh

    hasContrHomsRepr : hasContrHoms Representation'
    hasContrHomsRepr = hasContrHomsIsoCommaᴰ₂ YO* LiftPsh isFullyFaithfulYO*

  -- Presheaves that have a universal element viewed as property
  -- (morphisms ignore it).
  --
  -- A functor C → 𝓟up is equivalent to a functor R : C → 𝓟 and a
  -- universal element for each R ⟅ c ⟆
  --
  -- An object over P is a universal element
  -- Morphisms over nat trans. are trivial
  𝓟up = ∫C HasUniversalElt

  -- Presheaves equipped with a universal element as structure
  -- (morphisms preserve it)
  --
  -- A functor C → 𝓟us is the data of
  -- 1. A functor R : C → 𝓟
  -- 2. A functor F : C → D

  -- 3. A *natural* choice of elements for R c (F c) with F c as
  --    vertex
  --
  -- An object over P is a universal element η
  --
  -- Morphisms over nat trans α : P , η → Q , η' are morphisms
  -- f : η .vertex → η' .vertex
  -- That that "represent" α.
  -- Since η, η' are universal, this type is contractible
  𝓟us = ∫C WithUniversalElt

  -- Presheaves equipped with a representation viewed as
  -- structure
  --
  -- A functor C → 𝓟rs is the data of
  -- 1. A functor R : C → 𝓟
  -- 2. A functor F : C → D
  -- 3. A natural iso LiftF ∘F R ≅ LiftF ∘F Yo ∘F F
  --
  -- An object over P is an iso P ≅ Yo c
  --
  -- Morphisms over nat trans α : P , iso → Q , iso' are morphisms
  -- f : iso .cod → iso' .cod
  -- That that commute: iso' ∘ Yo f ≡ α ∘ iso
  -- because Yo is fully faithful, this is contractible.
  𝓟rs = ∫C Representation'

  -- Part 1: functoriality comes for free from contractibility
  coherence : Functor 𝓟up 𝓟us
  coherence = ∫F {F = Id} (mkContrHomsFunctor hasContrHomsWUE λ ue →
    ue .vertex , ue .element , ue .universal)

  -- Part 2: this is one direction of the equivalence between
  -- universal elements and representations, extended to a functor.
  --
  -- For this definition, we use mkFunctorᴰContrHoms' and
  -- change-contractum to ensure we get the "efficient" definition
  -- out.
  -- If we apply mkFunctorᴰContrHoms directly with our above proof,
  -- then the result will be f composed with an identity instead
  unYoneda : Functor 𝓟us 𝓟rs
  unYoneda = ∫F {F = Id} (mkContrHomsFunctor'
    (λ {x = P} (d , η , η-isUniv) →
        let r = universalElementToRepresentation D P (record
              { vertex = d
              ; element = η
              ; universal = η-isUniv }) in
        d , NatIso→FUNCTORIso (D ^op) _ (r .snd))
    λ {x = P}{y = Q}{f = α} {xᴰ = c-UE} {yᴰ = d-UE} (f , f-sq , tt) →
      let (c , ηP , _) = c-UE
          module d-UE = UniversalElementNotation (record
            { vertex = d-UE .fst
            ; element = d-UE .snd .fst
            ; universal = d-UE .snd .snd
            }) in
      change-contractum (hasContrHomsRepr α _ _) (f ,
        cong d-UE.intro ((cong (α ⟦ c ⟧) (funExt⁻ (P .F-id) ηP)) ∙ sym f-sq)
        ∙ sym d-UE.η))

  -- | TODO: this should be definable as some composition of
  -- | reassociativity and projection but need to implement those
  -- | functors
  ForgetUniversal : Functor 𝓟us (∫C Elt)
  ForgetUniversal .F-ob x = (x .snd .fst , (x .fst)) , (x .snd .snd .fst)
  ForgetUniversal .F-hom α = (α .snd .fst , (α .fst)) , (α .snd .snd .fst)
  ForgetUniversal .F-id = refl
  ForgetUniversal .F-seq _ _ = refl

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         {P : Profunctor C D ℓS}
         (ues : UniversalElements P)
         where
  private
    𝓟 = PresheafCategory D ℓS
    Pup : Functor C (𝓟up D ℓS)
    Pup = TotalCat.intro' P
      (mkContrHomsSection (hasContrHomsPropertyOver _ _) ues)

    Pus : Functor C (𝓟us D ℓS)
    Pus = coherence D ℓS ∘F Pup

    Prs : Functor C (𝓟rs D ℓS)
    Prs = unYoneda D ℓS ∘F Pus

    P-elt : Functor C (∫C {C = D ×C PresheafCategory D ℓS}
                          (Graph (Profunctor→Relatoro* Id)))
    P-elt = ForgetUniversal D ℓS ∘F Pus

    App : D o-[ ℓS ]-* 𝓟
    App = Profunctor→Relatoro* Id

    R = Profunctor→Relatoro* P

  FunctorComprehension : Functor C D
  FunctorComprehension = π₁ App ∘F P-elt

  -- The profunctor here is definitionally iso to R(F -, =), as we see below
  counit-elt' : NatElt (App ∘Flr ((π₁ App ^opF) ,
                        π₂ App) ∘Flr ((P-elt ^opF) , P-elt))
  counit-elt' = whisker (πElt App) P-elt

  open NatElt
  -- ∀ c . R (F ⟅ c ⟆) c, naturally
  counit-elt : NatElt (R ∘Fl (FunctorComprehension ^opF))
  counit-elt .N-ob = counit-elt' .N-ob
  counit-elt .N-hom× = counit-elt' .N-hom×
  counit-elt .N-ob-hom×-agree = counit-elt' .N-ob-hom×-agree
  counit-elt .N-natL = counit-elt' .N-natL
  counit-elt .N-natR = counit-elt' .N-natR

  private
    -- Test to show that counit-elt matches the original universal element

    -- This demonstrates that the selection of universal elements is
    -- natural with respect to the functorial action constructed from
    -- universality
    test-counit-elt-def : ∀ c → counit-elt .N-ob c ≡ ues c .element
    test-counit-elt-def c = refl

    LiftPsh = (postcomposeF (D ^op) (LiftF {ℓS}{ℓD'}))
    YO* = (postcomposeF (D ^op) (LiftF {ℓD'}{ℓS}) ∘F YO)

    ReAssoc : Functor (𝓟rs D ℓS) (IsoComma YO* LiftPsh)
    ReAssoc = Assoc-sl⁻ (IsoCommaᴰ YO* LiftPsh)

    P-iso : Functor C (∫C (IsoCommaᴰ YO* LiftPsh))
    P-iso = Assoc-sl⁻ (IsoCommaᴰ YO* LiftPsh) ∘F Prs

  ProfIso' : NatIso _ _
  ProfIso' = π≅ YO* LiftPsh ∘ˡⁱ P-iso

  ProfIso : NatIso (YO* ∘F FunctorComprehension) (LiftPsh ∘F P)
  ProfIso .trans .N-ob = ProfIso' .trans .N-ob
  ProfIso .trans .N-hom = ProfIso' .trans .N-hom
  ProfIso .nIso = ProfIso' .nIso
