{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Profunctor.General where

open import Cubical.Reflection.RecordEquiv

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor.Redundant
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
open import Cubical.Data.Sigma

open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Functors.More

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Functor
open UniversalElement
open Bifunctor

-- A profunctor, also called a distributor is a generalization of a
-- functor where the values are not objects of the codomain, but
-- instead presheaves
Profunctor : (C : Category ℓC ℓC')(D : Category ℓD ℓD') → ∀ ℓS → Type _
Profunctor C D ℓS = Functor C (PresheafCategory D ℓS)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (R : Profunctor C D ℓS) where

  open NatTrans
  open NatIso
  open isIsoC
  open isEquiv

  UniversalElements : Type _
  UniversalElements =
    ∀ (c : C .ob)
    → UniversalElement D (R ⟅ c ⟆)
