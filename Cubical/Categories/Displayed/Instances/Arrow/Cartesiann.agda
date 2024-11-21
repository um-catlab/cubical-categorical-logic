{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Arrow.Cartesiann where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.Functor
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Constructions.Reindex.Monoidal

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level

module _ {C : CartesianCategory ℓC ℓC'} {D : CartesianCategory ℓD ℓD'}
  (F G : CartesianFunctor (C .fst) (D .fst))
  where
  IsoComma : CartesianCategoryᴰ C {!!} {!!}
  IsoComma = {!reindex!}
