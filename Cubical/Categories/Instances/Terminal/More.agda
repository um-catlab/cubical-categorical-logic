{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Terminal.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Instances.Terminal


module _ {ℓC ℓ'C : Level} {C : Category ℓC ℓ'C} {ℓ*} where
  intro : Functor C (TerminalCategory {ℓ* = ℓ*})
  intro .Functor.F-ob = λ _ → tt*
  intro .Functor.F-hom x = refl
  intro .Functor.F-id = refl
  intro .Functor.F-seq f g = refl
