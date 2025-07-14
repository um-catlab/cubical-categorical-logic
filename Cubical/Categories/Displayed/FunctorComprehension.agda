{-# OPTIONS --safe --lossy-unification #-}
{--
 -- Displayed Functor Comprehension
 -- Construction of a Displayed Functor by defining displayed universal elements
 --}
module Cubical.Categories.Displayed.FunctorComprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.FunctorComprehension
open import Cubical.Data.Sigma

open import Cubical.Categories.Presheaf.Base

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Functors.More
import Cubical.Categories.Constructions.TotalCategory as TotalCat

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Functor
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
