{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Profunctor.FunctorComprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Displayed.Constructions.FullSubcategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Displayed.Preorder
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Constructions.Comma
open import Cubical.Categories.Displayed.Constructions.Graph
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Profunctor.Relator

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Functor
open UniversalElement
open NatIso
open NatTrans

module _ (D : Category ℓD ℓD') (ℓS : Level) where
  𝓟 = PresheafCategory D ℓS

  -- Presheaves that have a universal element viewed as property
  -- (morphisms ignore it).
  --
  -- A functor C → 𝓟up is equivalent to a functor R : C → 𝓟 and a
  -- universal element for each R ⟅ c ⟆
  --
  -- An object over P is a universal element
  -- Morphisms over nat trans. are trivial
  𝓟up : Categoryᴰ 𝓟 (ℓ-max (ℓ-max ℓD ℓD') ℓS) ℓ-zero
  𝓟up = FullSubcategoryᴰ 𝓟 (UniversalElement D)

  hasContrHoms𝓟up : hasContrHoms 𝓟up
  hasContrHoms𝓟up = hasContrHomsFullSubcategory _ _

  -- Presheaves equipped with a universal element as structure
  -- (morphisms preserve it)
  --
  -- A functor C → 𝓟us is the data of
  -- 1. A functor R : C → 𝓟
  -- 2. A functor F : C → D

  -- 3. A natural choice of universal elements for R ⟅ c ⟆ with F c as
  --    vertex
  -- 
  -- An object over P is a universal element η
  --
  -- Morphisms over nat trans α : P , η → Q , η' are morphisms
  -- f : η .vertex → η' .vertex
  -- That that "represent" α.
  -- Since η, η' are universal, this type is contractible.
  𝓟us : Categoryᴰ 𝓟 _ _
  𝓟us = ∫Cᴰ 𝓟elt 𝓟usᴰ  where
    𝓟elt : Categoryᴰ 𝓟 _ _
    𝓟elt = ∫Cᴰsl (Graph (Sym (CurriedToBifunctor Id)))

    𝓟usᴰ : Categoryᴰ (∫C 𝓟elt) _ _
    𝓟usᴰ = FullSubcategoryᴰ _
     (λ elt → isUniversal D (elt .fst)
                            (elt .snd .fst)
                            (elt .snd .snd))

  -- | TODO: this should be definable as some kind of functor
  -- | composition Fst ∘ Fst ∘ Snd, but need to implement those
  -- | combinators.
  𝓟us→D : Functor (∫C 𝓟us) D
  𝓟us→D .F-ob  x = x .snd .fst .fst
  𝓟us→D .F-hom f = f .snd .fst .fst
  𝓟us→D .F-id = refl
  𝓟us→D .F-seq _ _ = refl

  hasContrHoms𝓟us : hasContrHoms 𝓟us
  hasContrHoms𝓟us {c' = Q} α ((d , η) , univ) ((d' , η') , univ') =
    (((ue'.intro ((α ⟦ _ ⟧) η)) , ue'.β) , _)
    , λ ((g , sq) , tt) → Σ≡Prop (λ _ → isPropUnit)
      (Σ≡Prop (λ _ → (Q ⟅ _ ⟆) .snd _ _)
      (sym (ue'.η ∙ cong ue'.intro sq)))
    where
      module ue  = UniversalElementNotation
        (record { vertex = d ; element = η ; universal = univ })
      module ue' = UniversalElementNotation
        (record { vertex = d' ; element = η' ; universal = univ' })


  coherence : Functorᴰ Id 𝓟up 𝓟us
  coherence = mkFunctorᴰContrHoms hasContrHoms𝓟us
    (λ ue → (ue .vertex , (ue .element)) , (ue .universal))

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
  𝓟r : Categoryᴰ 𝓟 _ _
  𝓟r = IsoCommaᴰ₁
    (postcomposeF (D ^op) (LiftF {ℓS}{ℓD'}))
    (postcomposeF (D ^op) (LiftF {ℓD'}{ℓS}) ∘F YO)

  -- this follows from the proof in 
  -- Cubical.Categories.Displayed.Constructions.Comma for
  -- IsoCommaᴰ₁
  -- hasContrHoms𝓟r : hasContrHoms 𝓟r
  -- hasContrHoms𝓟r = hasContrHomsIsoCommaᴰ₁ _ _
  --   {!!}

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (R : Functor C (𝓟 D ℓS)) where

  open NatTrans
  open NatIso
  open isIsoC
  open isEquiv

  UniversalElements : Type _
  UniversalElements =
    ∀ (c : C .ob)
    → UniversalElement D (R ⟅ c ⟆)

Profunctor : (C : Category ℓC ℓC')(D : Category ℓD ℓD') → ∀ ℓS → Type _
Profunctor C D ℓS = Functor C (𝓟 D ℓS)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         {R : Profunctor C D ℓS}
         (ues : UniversalElements R)
         where
  private
    Rup : Functor C (∫C (𝓟up D ℓS))
    Rup = mk∫Functor R (mkFullSubcategoryᴰFunctorᴰ _ _ _ (λ _ → ues _))

  FunctorComprehension : Functor C D
  FunctorComprehension = 𝓟us→D D ℓS ∘F ∫F (coherence D ℓS) ∘F Rup

  -- TODO: use πElt to construct a natural element R (F c) c
  module _ where
    private
      F = FunctorComprehension
      BifR = CurriedToBifunctor R
    open NatElt
    open UniversalElementNotation
    counit-elt : NatElt (BifR ∘Fr (F ^opF))
    counit-elt .N-ob c =
      πElt BifR .N-ob ((c , (F ⟅ c ⟆)) , ues c .element)
    counit-elt .N-hom× {x}{y} f =
      R .F-hom f .N-ob (ues y .vertex) (ues y .element)
    counit-elt .N-ob-hom×-agree {x} =
      πElt BifR .N-ob-hom×-agree
    counit-elt .N-natL f = refl
    counit-elt .N-natR {x}{y} f =
      πElt BifR .N-natR ((_ , (F ⟪ f ⟫)) ,
      sym (ues x .universal (F ⟅ y ⟆)
        .equiv-proof _ .fst .snd))
