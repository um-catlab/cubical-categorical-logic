{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Gluing.Normalizationn where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Constructions.Free.CartesianCategory.Base hiding (rec)
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.Functor

private variable
  ℓq ℓq' : Level

module _ (Q : ×Quiver ℓq ℓq') where
  private module Q = ×QuiverNotation Q
  Cl : CartesianCategory _ _
  Cl = FreeCartesianCategory Q
  private
    module Cl = CartesianCategoryNotation Cl
  module _ {C : CartesianCategory {!!} {!!}} {D : CartesianCategory {!!} {!!}}
    (F : CartesianFunctor C D) where
