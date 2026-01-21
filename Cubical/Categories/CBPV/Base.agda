{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.CBPV.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open import Cubical.Categories.Enriched.NaturalTransformation.Base
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Functor

open EnrichedCategory

private
  variable
    ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm : Level

record CBPVModel (ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm : Level) :
  Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max
    (ℓ-suc (ℓ-suc ℓC))
    (ℓ-suc (ℓ-suc ℓC')))
    (ℓ-suc ℓVTy))
    (ℓ-suc ℓVTm))
    (ℓ-suc ℓCTy))
    (ℓ-suc (ℓ-suc ℓCTm)))
  where
  field
    Scwf : SCwF ℓC ℓC' ℓVTy ℓVTm
  C = Scwf .fst
  V = PshMon.𝓟Mon C ℓCTm
  field
    Stacks : EnrichedCategory V ℓCTy
    CTm : EnrichedFunctor V Stacks (self C _)
