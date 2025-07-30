{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.CartesianClosed.Base where

open import Cubical.Categories.Category
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

record CartesianClosedCategory (ℓ ℓ' : Level) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  field
    CC : CartesianCategory ℓ ℓ'
  -- potential performance issue
  open CartesianCategory CC
  field
    exps : AllExponentiable C bp

