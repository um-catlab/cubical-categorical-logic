{-
  Enhancement of IsoFiber to a displayed cartesian category
  when the functor F : C → D is a cartesian functor
-}
module Cubical.Categories.Displayed.Constructions.IsoFiber.Cartesian where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.Functor

import Cubical.Categories.Displayed.Constructions.IsoFiber.Base as |IsoFiber|
open import Cubical.Categories.Displayed.Limits.Cartesian

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : CartesianCategory ℓC ℓC'} {D : CartesianCategory ℓD ℓD'}
  (F : CartesianFunctor (C .fst) (D .fst))
  where
  private
    module C = CartesianCategoryNotation C
    module D = CartesianCategoryNotation D
    IsoFiber : CartesianCategoryᴰ D {!!} {!!}
    IsoFiber = {!!}
