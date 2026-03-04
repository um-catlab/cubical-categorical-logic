{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Instances.BinProduct.Redundant.Assoc where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base hiding (Id)
open import Cubical.Data.Sigma

import Cubical.Categories.Instances.BinProduct.Redundant.Assoc.ToRight
  as ToRight
import Cubical.Categories.Instances.BinProduct.Redundant.Assoc.ToLeft
  as ToLeft
open import Cubical.Categories.Instances.BinProduct.Redundant.Base as BP
open import Cubical.Categories.Instances.Free.Category.Quiver as Free
  hiding (rec)
open import Cubical.Categories.Bifunctor

private
  variable
    ℓc ℓc' ℓd ℓd' ℓe ℓe' ℓf ℓf' : Level

module _ {C : Category ℓc ℓc'}
         {D : Category ℓd ℓd'}{E : Category ℓe ℓe'}{F : Category ℓf ℓf'} where
  assoc-bif : Bifunctor (C ×C D) E F → Bifunctor C (D ×C E) F
  assoc-bif G = Functor→Bifunctor (rec (C ×C D) E G ∘F ToLeft.Assoc)

  assoc-bif⁻ : Bifunctor C (D ×C E) F → Bifunctor (C ×C D) E F
  assoc-bif⁻ G = Functor→Bifunctor (rec C (D ×C E) G ∘F ToRight.Assoc)
