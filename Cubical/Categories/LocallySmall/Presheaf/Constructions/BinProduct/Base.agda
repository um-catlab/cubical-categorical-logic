module Cubical.Categories.LocallySmall.Presheaf.Constructions.BinProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

import Cubical.Categories.Constructions.BinProduct.Redundant.Base as R

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Presheaf.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Set
open import Cubical.Categories.LocallySmall.Instances.Functor
open import Cubical.Categories.LocallySmall.Instances.Functor.Properties
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
open import Cubical.Categories.LocallySmall.Bifunctor.Base
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Functor.Constant
open import Cubical.Categories.LocallySmall.NaturalTransformation.Base

open import Cubical.Categories.LocallySmall.Displayed
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Bisection
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base

open Category
open Categoryᴰ
open Σω
open Liftω

module _ (C : SmallCategory ℓC ℓC') where
  private
    module SET = CategoryᴰNotation SET
    ∫SET = ∫C SET
    module ∫SET = CategoryNotation ∫SET
    PSH = PRESHEAF C
    module PSH = CategoryᴰNotation PSH

    _⊗_ = R._×C_
    Csmall = SmallLocallySmallCategory→SmallCategory C

  open Functorᴰ
  PshProd' : Functorᴰ ℓ-MAX (PSH ×Cᴰ PSH) PSH
  PshProd' = postcomposeF _ _ ×SET ∘Fᴰ ,F-SFFunctorⱽ (C ^opsmall) SET SET

  PshProdᴰ : Bifunctorᴰ (ParFunctorToBifunctor ℓ-MAX) PSH PSH PSH
  PshProdᴰ = ParFunctorᴰToBifunctorᴰ PshProd'

  PshProd : Bifunctor PSH.∫C PSH.∫C PSH.∫C
  PshProd = Bifunctorᴰ.∫F PshProdᴰ
