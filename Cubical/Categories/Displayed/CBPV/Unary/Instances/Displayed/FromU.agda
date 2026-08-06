-- The displayed CBPV category induced by a displayed functor Uᴰ.
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Displayed.FromU where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Displayed.FromProf
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.FromProf

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

module _ {C : Category ℓ ℓ'} {V : Category ℓ ℓ'}
  (U : Functor C V)
  {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'} {Vᴰ : Categoryᴰ V ℓᴰ ℓᴰ'}
  (Uᴰ : Functorᴰ U Cᴰ Vᴰ) where

  U→CBPVᴰ : CBPVCatᴰ (U→CBPV U) ℓᴰ ℓᴰ'
  U→CBPVᴰ = Prof→CBPVᴰ (YOᴰ ∘Fᴰ Uᴰ)
