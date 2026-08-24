open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hSet)

module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations
  (V : hSet ℓ-zero) where

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Base V public
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.GetSet V public
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Alloc V public
