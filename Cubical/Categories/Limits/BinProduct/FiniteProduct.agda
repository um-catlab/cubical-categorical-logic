{-# OPTIONS --lossy-unification #-}
{-

  This is one of several possible definitions of the binary product.
  It turns out to be the best.

-}
module Cubical.Categories.Limits.BinProduct.FiniteProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma as Ty hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor
-- open import Cubical.Categories.FunctorComprehension
-- open import Cubical.Categories.NaturalTransformation
-- open import Cubical.Categories.Profunctor.General
-- open import Cubical.Categories.Presheaf.Base
-- open import Cubical.Categories.Presheaf.Representable
-- open import Cubical.Categories.Presheaf.Representable.More
-- open import Cubical.Categories.Bifunctor as R hiding (Fst; Snd)

-- open import Cubical.Categories.Presheaf.More
-- open import Cubical.Categories.Presheaf.Morphism.Alt
-- open import Cubical.Categories.Presheaf.Constructions hiding (π₁; π₂)
-- open import Cubical.Categories.Yoneda

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
-- open PshHom

module _ (C : Category ℓ ℓ') where
