{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.Constructions.BinProduct.Redundant.Assoc where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base hiding (Id)
open import Cubical.Categories.Instances.Functors.Redundant
open import Cubical.Categories.Instances.Functors.Redundant.Bifunctor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Graph.Base
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.Sigma

import Cubical.Categories.Constructions.BinProduct.Redundant.Assoc.ToRight
  as ToRight
import Cubical.Categories.Constructions.BinProduct.Redundant.Assoc.ToLeft
  as ToLeft
open import Cubical.Categories.Constructions.BinProduct.Redundant.Base as BP
open import Cubical.Categories.Constructions.Free.Category.Quiver as Free
  hiding (rec)
open import Cubical.Categories.Constructions.Presented as Presented hiding (rec)
open import Cubical.Categories.Bifunctor.Redundant

private
  variable
    ℓc ℓc' ℓd ℓd' ℓe ℓe' ℓf ℓf' : Level

module _ {C : Category ℓc ℓc'}
         {D : Category ℓd ℓd'}{E : Category ℓe ℓe'}{F : Category ℓf ℓf'} where
  assoc-bif : Bifunctor (C ×C D) E F → Bifunctor C (D ×C E) F
  assoc-bif G = Functor→Bifunctor (rec (C ×C D) E G ∘F ToLeft.Assoc)
