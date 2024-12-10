{-
  Enhancement of IsoFiber to a displayed cartesian category
  when the functor F : C → D is a cartesian functor
-}
module Cubical.Categories.Displayed.Constructions.IsoFiber.Cartesian where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.Functor

import Cubical.Categories.Displayed.Constructions.IsoFiber.Base as |IsoFiber|
open import Cubical.Categories.Displayed.Constructions.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Arrow.Base hiding (Iso)
open import Cubical.Categories.Displayed.Instances.Arrow.Properties
open import Cubical.Categories.Displayed.Instances.Arrow.Cartesian
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryR.Cartesian

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : CartesianCategory ℓC ℓC'} {D : CartesianCategory ℓD ℓD'}
  (F : CartesianFunctor (C .fst) (D .fst))
  where
  IsoFiber : CartesianCategoryᴰ D _ _
  IsoFiber = ∫Cᴰsr D C (reindex (Iso D) (_×F_ {A = D} {C = C} (IdCF {C = D}) F) (hasPropHomsIso _) (isIsoFibrationIso _))
  private
    test : IsoFiber .fst ≡ |IsoFiber|.IsoFiber (F .CartesianFunctor.|F|)
    test = refl
