{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Sets.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets

private
  variable
    ℓ ℓ' : Level

open Functor
-- Lift functor
LiftF : Functor (SET ℓ) (SET (ℓ-max ℓ ℓ'))
LiftF {ℓ}{ℓ'} .F-ob A = (Lift {ℓ}{ℓ'} (A .fst)) , isOfHLevelLift 2 (A .snd)
LiftF .F-hom f x = lift (f (x .lower))
LiftF .F-id = refl
LiftF .F-seq f g = funExt λ x → refl

