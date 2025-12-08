{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Presheaf.GloballySmall.PresheavesOnPresheaves where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.HLevels

import Cubical.Data.Equality as Eq

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Functor.SmallFibers.Base
open import Cubical.Categories.LocallySmall.NaturalTransformation.SmallFibers
open import Cubical.Categories.LocallySmall.Presheaf.GloballySmall.IntoFiberCategory.Base

open import Cubical.Categories.LocallySmall.Displayed.Category
open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base

module _ (C : SmallCategory ℓC ℓC') where
  private
    module C = SmallCategory C
    module C^op = SmallCategory (C ^opsmall)

  PRESHEAF-OVER-LIFTABLE-LEVEL : SmallFibersCategoryᴰ LIFTABLE-LEVEL _ _ _
  PRESHEAF-OVER-LIFTABLE-LEVEL =
    reindexEq LIFTABLE-LEVEL-π (SMALL-PRESHEAF C) Eq.refl λ _ _ → Eq.refl

  PRESHEAF-ON-PRESHEAF : Categoryᴰ {!!} {!!} {!!}
  PRESHEAF-ON-PRESHEAF = FUNCTOR {!PRESHEAF-OVER-LIFTABLE-LEVEL!} {!!} {!!}
