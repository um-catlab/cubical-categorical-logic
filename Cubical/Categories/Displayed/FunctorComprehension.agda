{-# OPTIONS --lossy-unification #-}
{--
 -- Displayed Functor Comprehension
 -- Construction of a Displayed Functor by defining displayed universal elements
 --}
module Cubical.Categories.Displayed.FunctorComprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.FunctorComprehension

import Cubical.Categories.Instances.TotalCategory as TotalCat

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.Presheaf
import Cubical.Categories.Displayed.Reasoning as Reasoning

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level
    ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓSᴰ : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         {P : Profunctor C D ℓS}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (Pᴰ : Profunctorᴰ P Cᴰ Dᴰ ℓSᴰ)
         {ues : UniversalElements P}
         (uesᴰ : UniversalElementsᴰ ues Pᴰ)
       where
  private
    ∫FunctorComprehension : Functor (TotalCat.∫C Cᴰ) (TotalCat.∫C Dᴰ)
    ∫FunctorComprehension =
      FunctorComprehension (∫Prof Pᴰ) (∫ues Pᴰ uesᴰ)
    module Dᴰ = Reasoning Dᴰ

  open Functor
  open Functorᴰ
  FunctorᴰComprehension : Functorᴰ (FunctorComprehension P ues) Cᴰ Dᴰ
  FunctorᴰComprehension .F-obᴰ xᴰ = (∫FunctorComprehension ⟅ _ , xᴰ ⟆) .snd
  FunctorᴰComprehension .F-homᴰ fᴰ = (∫FunctorComprehension ⟪ _ , fᴰ ⟫) .snd
  FunctorᴰComprehension .Functorᴰ.F-idᴰ =
    Dᴰ.rectify $ Dᴰ.≡out (∫FunctorComprehension .F-id)
  FunctorᴰComprehension .Functorᴰ.F-seqᴰ fᴰ gᴰ =
    Dᴰ.rectify $ Dᴰ.≡out $ ∫FunctorComprehension .F-seq (_ , fᴰ) (_ , gᴰ)

module _ {C : Category ℓC ℓC'}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
         {Pᴰ : Profunctorⱽ Cᴰ Dᴰ ℓSᴰ}
         (uesⱽ : UniversalElementsⱽ Pᴰ) where

  -- WARNING: the following definition uses reindexing on
  -- morphisms. There's no way around this without a "primitive"
  -- vertical composition.
  FunctorⱽComprehension : Functorⱽ Cᴰ Dᴰ
  FunctorⱽComprehension = reindF'' _ Eq.refl
    (implicitFunExt (implicitFunExt (funExt (Category.⋆IdL C)))) $
    FunctorᴰComprehension Pᴰ λ x xᴰ →
      UniversalElementⱽ.toUniversalᴰ (uesⱽ x xᴰ)
