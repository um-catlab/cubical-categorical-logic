{-# OPTIONS --safe --lossy-unification #-}
{-

  These are some alternative definitions of CartesianProduct.

-}
module Cubical.Categories.Limits.BinProduct.Adjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma as Ty hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
import Cubical.Categories.Constructions.BinProduct.Redundant.Base as R
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Bifunctor as R hiding (Fst; Snd)

open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Yoneda

private
  variable
    ℓ ℓ' : Level
  _⊗_ = R._×C_

module _ (C : Category ℓ ℓ') where
  -- these definitions of BinProduct aren't as nice as the one in
  -- BinProduct.More because they give a worse definition when fixing
  -- one side.
  BinProduct = RightAdjointAt (Δ C)
  BinProducts = RightAdjoint (Δ C)

  private
    -- This definition looks promising at first, but doesn't give the
    -- right behavior for BinProductWithF ⟪_⟫
    BadBinProductProf : Profunctor (C R.×C C) C ℓ'
    BadBinProductProf =
      (precomposeF _ (Δ C ^opF) ∘F YO) ∘F R.RedundantToProd C C

    -- This definition is *almost* exactly the same as the next one,
    -- except using ∘F YO ×F YO vs ∘Flr YO , YO. But it has the same
    -- problem as the previous. That ∘F vs ∘Flr makes all the difference.
    AlsoBadBinProductProf : Profunctor (C ⊗ C) C ℓ'
    AlsoBadBinProductProf =
      R.rec C C (ParFunctorToBifunctor (PshProd' ∘F (YO ×F YO)))
