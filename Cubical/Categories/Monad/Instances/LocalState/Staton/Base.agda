{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.Categories.Monad.Instances.LocalState.Staton.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.Instances.Injections
open import Cubical.Categories.Instances.Schanuel
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Pullback.More

import Cubical.Categories.Monad.Instances.LocalState.PlotkinPower.Base as PP

open Functor

module _ {ℓ : Level} (V : hSet ℓ) where

  T-preservesPullbacks :
    (A : Functor Inj (SET ℓ)) →
    PreservesPullbacks A →
    PreservesPullbacks (PP.T V .F-ob A)
  T-preservesPullbacks A A-pb = {! !}

  -- misleading def
  StatonT : Functor (Schanuel ℓ) (Schanuel ℓ)
  StatonT = MapFullSubcategory
    ([Inj,Set] ℓ) (PreservesPullbacks {C = Inj} {D = SET ℓ})
    ([Inj,Set] ℓ) (PreservesPullbacks {C = Inj} {D = SET ℓ})
    (PP.T V)
    T-preservesPullbacks
