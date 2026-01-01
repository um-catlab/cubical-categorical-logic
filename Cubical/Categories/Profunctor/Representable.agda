-- A profunctor P : C -/-> D is representable by a functor F : C -> D
-- when P ≅ YO ∘F F
--
-- In general, P and Yo ∘F F are presheaves of different universe
-- levels, so we need to use ProfHom in this definition

{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Profunctor.Representable where

open import Cubical.Reflection.RecordEquiv

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.ComposeProperty
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Bifunctor as Bif
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.HomFunctor

open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Yoneda

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓS ℓR : Level

open Category
open Bifunctor

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  private
    module C = Category C
    module D = Category D

  module _ (F : Functor C D) (P : Profunctor C D ℓP) where
    private
      module P = ProfunctorNotation P
    _RepresentsProf_ : Type _
    _RepresentsProf_ = ProfunctorIso (YO ∘F F) P

    -- To show Yo ∘ F ≅ P
    -- It should suffice to show
    -- 1. ue : ∀ c → Yo ⟅ F ⟅ c ⟆ ⟆ ≅ P ⟅ c ⟆
    --    so ue c .intro : P d c → D [ d , F ⟅ c ⟆ ]
    --    and ue c .element : P (F c) c
    -- 2. this definition is natural

    -- This naturality condition should also be equivalent to showing
    -- that F ⟪ f ⟫ : D [ F c , F c' ]
    --   is equivalent to
    --   ue c' .intro (ue c .element P.⋆ʳ f) ≡ F ⟪ f ⟫
    --   or equivalently that
    --   ue c .element P.⋆ʳ f ≡ F ⟪ f ⟫ P.⋆ˡ ue c .element
    --   i.e., naturality lol

    -- to construct a _RepresentsProf_ it suffices to provide a family
    -- of universal elements that are *natural*. Naturality of the
    -- universal element is equivalent to showing that the
    -- functoriality agrees with the "induced" functoriality
    -- definition.

  -- by the fact that Yoneda is FF and postcomposition by a FF functor is FF
  -- plus some coercions
  YO-FF-ProfIso : {F G : Functor C D}
    → ProfunctorIso (YO ∘F F) (YO ∘F G)
    → NatIso F G
  YO-FF-ProfIso {F}{G} YF≅YG =
    FUNCTORIso→NatIso C D $
    liftIso {F = postcomposeF C YO} (isFullyFaithfulPostcomposeF {G = YO} isFullyFaithfulYO) $
    NatIso→FUNCTORIso C (PresheafCategory D ℓD') $
    ProfunctorIso→NatIso YF≅YG
