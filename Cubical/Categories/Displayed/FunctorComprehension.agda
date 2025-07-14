{-# OPTIONS --safe  --lossy-unification #-}
{--
 -- Displayed Functor Comprehension
 -- Construction of a Displayed Functor by defining displayed universal elements
 --}
module Cubical.Categories.Displayed.FunctorComprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.FunctorComprehension

import Cubical.Categories.Constructions.TotalCategory as TotalCat

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Profunctor
import Cubical.Categories.Displayed.Reasoning as Reasoning

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level
    ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓSᴰ : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         {P : Profunctor C D ℓS}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         {Pᴰ : Profunctorᴰ P Cᴰ Dᴰ ℓSᴰ}
         {ues : UniversalElements P}
         (uesᴰ : UniversalElementsᴰ ues Pᴰ)
       where
  private
    ∫FunctorComprehension : Functor (TotalCat.∫C Cᴰ) (TotalCat.∫C Dᴰ)
    ∫FunctorComprehension =
      FunctorComprehension (∫UEs Pᴰ uesᴰ :> UniversalElements (∫Prof Pᴰ))
    module Dᴰ = Reasoning Dᴰ

  open Functor
  open Functorᴰ
  FunctorᴰComprehension : Functorᴰ (FunctorComprehension ues) Cᴰ Dᴰ
  FunctorᴰComprehension .F-obᴰ xᴰ = (∫FunctorComprehension ⟅ _ , xᴰ ⟆) .snd
  FunctorᴰComprehension .F-homᴰ fᴰ = (∫FunctorComprehension ⟪ _ , fᴰ ⟫) .snd
  FunctorᴰComprehension .Functorᴰ.F-idᴰ =
    Dᴰ.rectify $ Dᴰ.≡out (∫FunctorComprehension .F-id)
  FunctorᴰComprehension .Functorᴰ.F-seqᴰ fᴰ gᴰ =
    Dᴰ.rectify $ Dᴰ.≡out $ ∫FunctorComprehension .F-seq (_ , fᴰ) (_ , gᴰ)
