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

-- module _ {D : Category ℓD ℓD'} ℓ ℓ' where
--   LiftPsh : Functor (PresheafCategory D ℓ) (PresheafCategory D (ℓ-max ℓ ℓ'))
--   LiftPsh = postcomposeF (D ^op) LiftF

--   isFullyFaithfulLiftPsh : isFullyFaithful LiftPsh
--   isFullyFaithfulLiftPsh = {!!}

-- module _ (ℓS : Level) {ℓE ℓE' : Level} {E : Category ℓE ℓE'} where
--   YO* : Functor E (PresheafCategory E (ℓ-max ℓE' ℓS))
--   YO* = LiftPsh _ _ ∘F YO

--   isFullyFaithfulYO* : isFullyFaithful YO*
--   isFullyFaithfulYO* = {!!}

-- module _ (D : Category ℓD ℓD') (ℓS : Level) where
--   𝓟 = PresheafCategory D ℓS

--   -- | TODO: reformulate FullSubcategory as a Categoryᴰ
--   𝓟u : Category _ _
--   𝓟u = FullSubcategory 𝓟 (UniversalElement D)

--   πu : Functor 𝓟u 𝓟
--   πu .F-ob = fst
--   πu .F-hom = λ z → z
--   πu .F-id = refl
--   πu .F-seq _ _ = refl

--   πues : (Pu : 𝓟u .ob) → UniversalElement D (πu ⟅ Pu ⟆)
--   πues = snd

--   module _ {P Q : 𝓟 .ob} (α : 𝓟 [ P , Q ])
--     (Pr : Representation D P) (Qr : Representation D Q)
--     where
--     RepresentationMorphism : Type _
--     RepresentationMorphism =
--       Σ[ f ∈ D [ Pr .fst , Qr .fst ] ]
--       Pr .snd .trans ⋆⟨ PresheafCategory D _ ⟩ LiftPsh _ _ ⟪ α ⟫
--       ≡ YO* _ ⟪ f ⟫ ⋆⟨ PresheafCategory D _ ⟩ Qr .snd .trans

--     private
--       RepresentationMorphism' : Type _
--       RepresentationMorphism' = fiber (YO* _ ⟪_⟫)
--         ((Pr .snd .trans ⋆⟨ PresheafCategory D _ ⟩ LiftPsh _ _ ⟪ α ⟫) ⋆⟨ PresheafCategory D _ ⟩
--         symNatIso (Qr .snd) .trans)

--       -- TODO: move these proofs to
--       RM→RM' : RepresentationMorphism → RepresentationMorphism'
--       RM→RM' (f , sq) = f , {!!}

--       RM'→RM : RepresentationMorphism' → RepresentationMorphism
--       RM'→RM (f , sq) = f , {!!}

--     isContrRM : isContr RepresentationMorphism
--     isContrRM =
--       isContrRetract RM→RM' RM'→RM (λ (f , _) → Σ≡Prop (λ f → PresheafCategory D _ .isSetHom
--         (Pr .snd .trans ⋆⟨ PresheafCategory D _ ⟩ LiftPsh _ _ ⟪ α ⟫)
--         (YO* _ ⟪ f ⟫ ⋆⟨ PresheafCategory D _ ⟩ Qr .snd .trans))
--         refl)
--         (isFullyFaithfulYO* _ _ _ .equiv-proof _)

--   open Preorderᴰ
--   -- | TODO: don't do this manually, instead define 𝓟rᴰ as an IsoCommaᴰ₁
--   -- | in Cubical.Categories.Displayed.Constructions.Comma
--   𝓟rᴰ : Preorderᴰ 𝓟 _ _
--   𝓟rᴰ .ob[_] P = Representation D P
--   𝓟rᴰ .Hom[_][_,_] {x = P}{y = Q} = RepresentationMorphism
--   𝓟rᴰ .idᴰ {P}{Pr} = (D .id) , {!!}
--   𝓟rᴰ ._⋆ᴰ_ (f , fsq) (g , gsq) = (f ⋆⟨ D ⟩ g) , {!!}
--   -- it's actually contractible
--   𝓟rᴰ .isPropHomᴰ {x}{y}{f}{xᴰ}{yᴰ} = isContr→isProp (isContrRM _ xᴰ yᴰ)

--   𝓟r : Category _ _
--   𝓟r = ∫C (Preorderᴰ→Catᴰ 𝓟rᴰ)

--   -- | TODO: reformulate this as a Functorᴰ over IdF {𝓟}
--   coherence : Functor 𝓟u 𝓟r
--   coherence .F-ob (P , η) .fst = P
--   coherence .F-ob (P , η) .snd = universalElementToRepresentation D P η
--   coherence .F-hom {x = (P , ηP)}{y = (Q , ηQ)} α =
--     α , {!!} 
--     -- this is very slightly "optimized" definition that we get from
--     -- contractibility. Leverage that!!!
--     -- , ηQ.intro (α .N-ob _ (ηP .element))
--     -- , {!!} -- 
--     -- , makeNatTransPath (funExt (λ d → funExt (λ (lift f) → cong lift
--     --   -- @Steven, this is already essentially proven in General.agda somewhere
--     --   -- basically that the universal element is a natural transformation
--     --   {!α .N-hom f!})))
--     where
--       module ηP = UniversalElementNotation ηP
--       module ηQ = UniversalElementNotation ηQ
--   -- These two should follow from the proof above that 𝓟rᴰ is contractible
--   coherence .F-id {P , η} = {!!}
--     -- Σ≡Prop (λ α → isContr→isProp (isContrRM _ repr repr))
--     --        refl
--     -- where repr = universalElementToRepresentation D P η
--   coherence .F-seq {P , ηP}{Q , ηQ}{R , ηR} α β = {!!}
--     -- Σ≡Prop ((λ α → isContr→isProp (isContrRM _ Pr Rr)))
--     --        refl
--     -- where Pr = universalElementToRepresentation D P ηP
--     --       Rr = universalElementToRepresentation D R ηR

--   πr𝓟 : Functor 𝓟r 𝓟
--   πr𝓟 = Fst

--   πrD : Functor 𝓟r D
--   πrD .F-ob (P , d , rep) = d
--   πrD .F-hom (α , f , sq) = f
--   πrD .F-id = refl
--   πrD .F-seq _ _ = refl

--   πr⇒ : NatIso (YO* ℓS ∘F πrD) (LiftPsh ℓS ℓD' ∘F πr𝓟)
--   πr⇒ .trans .N-ob (P , d , rep) = rep .trans
--   πr⇒ .trans .N-hom (α , f , sq) = makeNatTransPath (sym (cong N-ob sq))
--   πr⇒ .nIso (P , d , rep) = FUNCTORIso _ _ _ (rep .nIso)
