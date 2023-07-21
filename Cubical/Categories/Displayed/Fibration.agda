{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Fibration where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where
  CartesianLift : (∫C (C /C (Fst {Cᴰ = D}))) .ob → Type _
  CartesianLift (c , (d , f)) = LocalRightAdjointAtᴰ (cod D) (d , f)

  isFibration : Type _
  isFibration = LocalRightAdjointᴰ (cod D)
