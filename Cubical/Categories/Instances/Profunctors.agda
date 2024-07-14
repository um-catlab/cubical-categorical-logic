{-
  For fixed C, D and ℓS, the category of profunctors C o-[ ℓS ]-* D
  and their homomorphisms.
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Profunctors where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.ChangeOfObjects
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator
-- open import Cubical.Categories.Profunctor.Homomorphism.Unary

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') ℓS where
  private
    PROF = C o-[ ℓS ]-* D

  PROFUNCTOR : Category _ _
  PROFUNCTOR = ChangeOfObjects (FUNCTOR ((C ^op) ×C D) (SET ℓS))
    (BifunctorToParFunctor {C = C ^op}{D = D}{E = SET ℓS})
