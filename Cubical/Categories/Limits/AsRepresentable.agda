{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.AsRepresentable where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Bifunctor as Bif
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Morphism
open import Cubical.Categories.Adjoint.UniversalElements

open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓj ℓj' ℓc ℓc' : Level

limit : {C : Category ℓc ℓc'}{J : Category ℓj ℓj'}
        (D : Functor J C)
      → Type _
limit {C = C}{J = J} = RightAdjointAt (λFR Bif.Fst)

limitsOfShape : (C : Category ℓc ℓc') (J : Category ℓj ℓj')
              → Type _
limitsOfShape C J = RightAdjoint {C = C} {D = (FUNCTOR J C)} (λFR Bif.Fst)

-- TODO: All functors preserve cones
--       Functors with left adjoints preserve limiting cones
