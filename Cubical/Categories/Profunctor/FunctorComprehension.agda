{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Profunctor.FunctorComprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Displayed.Preorder
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Yoneda

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Functor
open UniversalElement
open NatIso
open NatTrans

module _ {D : Category ℓD ℓD'} ℓ ℓ' where
  LiftPsh : Functor (PresheafCategory D ℓ) (PresheafCategory D (ℓ-max ℓ ℓ'))
  LiftPsh = postcomposeF (D ^op) LiftF

  isFullyFaithfulLiftPsh : isFullyFaithful LiftPsh
  isFullyFaithfulLiftPsh = {!!}

module _ (ℓS : Level) {ℓE ℓE' : Level} {E : Category ℓE ℓE'} where
  YO* : Functor E (PresheafCategory E (ℓ-max ℓE' ℓS))
  YO* = LiftPsh _ _ ∘F YO

  isFullyFaithfulYO* : isFullyFaithful YO*
  isFullyFaithfulYO* = {!!}

module _ (D : Category ℓD ℓD') (ℓS : Level) where
  𝓟 = PresheafCategory D ℓS

  𝓟u : Category _ _
  𝓟u = FullSubcategory 𝓟 (UniversalElement D)

  πu : Functor 𝓟u 𝓟
  πu .F-ob = fst
  πu .F-hom = λ z → z
  πu .F-id = refl
  πu .F-seq _ _ = refl

  πues : (Pu : 𝓟u .ob) → UniversalElement D (πu ⟅ Pu ⟆)
  πues = snd

  module _ {P Q : 𝓟 .ob} (α : 𝓟 [ P , Q ])
    (Pr : Representation D P) (Qr : Representation D Q)
    where
    RepresentationMorphism : Type _
    RepresentationMorphism =
      Σ[ f ∈ D [ Pr .fst , Qr .fst ] ]
      Pr .snd .trans ⋆⟨ PresheafCategory D _ ⟩ LiftPsh _ _ ⟪ α ⟫
      ≡ YO* _ ⟪ f ⟫ ⋆⟨ PresheafCategory D _ ⟩ Qr .snd .trans

    private
      RepresentationMorphism' : Type _
      RepresentationMorphism' = fiber (YO* _ ⟪_⟫)
        ((Pr .snd .trans ⋆⟨ PresheafCategory D _ ⟩ LiftPsh _ _ ⟪ α ⟫) ⋆⟨ PresheafCategory D _ ⟩
        symNatIso (Qr .snd) .trans)

      -- TODO: slide an iso around a square
      RM→RM' : RepresentationMorphism → RepresentationMorphism'
      RM→RM' (f , sq) = f , {!!}

      -- TODO: slide an iso around a square
      RM'→RM : RepresentationMorphism' → RepresentationMorphism
      RM'→RM (f , sq) = f , {!!}

    isContrRM : isContr RepresentationMorphism
    isContrRM =
      isContrRetract RM→RM' RM'→RM (λ (f , _) → Σ≡Prop (λ f → PresheafCategory D _ .isSetHom
        (Pr .snd .trans ⋆⟨ PresheafCategory D _ ⟩ LiftPsh _ _ ⟪ α ⟫)
        (YO* _ ⟪ f ⟫ ⋆⟨ PresheafCategory D _ ⟩ Qr .snd .trans))
        refl)
        (isFullyFaithfulYO* _ _ _ .equiv-proof _)

  open Preorderᴰ
  𝓟rᴰ : Preorderᴰ 𝓟 _ _
  𝓟rᴰ .ob[_] P = Representation D P
  𝓟rᴰ .Hom[_][_,_] {x = P}{y = Q} = RepresentationMorphism
  -- EZ
  𝓟rᴰ .idᴰ {P}{Pr} = (D .id) , {!!}
  -- Just pasting of commutative squares
  𝓟rᴰ ._⋆ᴰ_ (f , fsq) (g , gsq) = (f ⋆⟨ D ⟩ g) , {!!}
  -- it's actually contractible
  𝓟rᴰ .isPropHomᴰ {x}{y}{f}{xᴰ}{yᴰ} = isContr→isProp (isContrRM _ xᴰ yᴰ)

  𝓟r : Category _ _
  𝓟r = ∫C (Preorderᴰ→Catᴰ 𝓟rᴰ)

  coherence : Functor 𝓟u 𝓟r
  coherence .F-ob (P , η) .fst = P
  coherence .F-ob (P , η) .snd = universalElementToRepresentation D P η
  coherence .F-hom {x = (P , ηP)}{y = (Q , ηQ)} α =
    α
    , ηQ.intro (α .N-ob _ (ηP .element))
    , makeNatTransPath (funExt (λ d → funExt (λ (lift f) → cong lift
      -- @Steven, this is already essentially proven in General.agda somewhere
      -- basically that the universal element is a natural transformation
      {!α .N-hom f!})))
    where
      module ηP = UniversalElementNotation ηP
      module ηQ = UniversalElementNotation ηQ
  -- These two should follow from the proof above that 𝓟rᴰ is contractible
  coherence .F-id {P , η} =
    Σ≡Prop (λ α → isContr→isProp (isContrRM _ repr repr))
           refl
    where repr = universalElementToRepresentation D P η
  coherence .F-seq {P , ηP}{Q , ηQ}{R , ηR} α β =
    Σ≡Prop ((λ α → isContr→isProp (isContrRM _ Pr Rr)))
           refl
    where Pr = universalElementToRepresentation D P ηP
          Rr = universalElementToRepresentation D R ηR

  πr𝓟 : Functor 𝓟r 𝓟
  πr𝓟 = Fst

  πrD : Functor 𝓟r D
  πrD .F-ob (P , d , rep) = d
  πrD .F-hom (α , f , sq) = f
  πrD .F-id = refl
  πrD .F-seq _ _ = refl

  πr⇒ : NatIso (YO* ℓS ∘F πrD) (LiftPsh ℓS ℓD' ∘F πr𝓟)
  πr⇒ .trans .N-ob (P , d , rep) = rep .trans
  πr⇒ .trans .N-hom (α , f , sq) = makeNatTransPath (sym (cong N-ob sq))
  πr⇒ .nIso (P , d , rep) = FUNCTORIso _ _ _ (rep .nIso)
