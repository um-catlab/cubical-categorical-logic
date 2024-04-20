{-# OPTIONS --safe #-}
module Cubical.Categories.Double.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.HLevel1Homs
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Constructions.Pullback

private
  variable
    ℓv ℓv' ℓsq ℓsq' : Level

record LocallyThinDoubleCategory ℓv ℓv' ℓsq ℓsq'
  : Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓv') (ℓ-max ℓsq ℓsq'))) where
  field
    V  : Category ℓv ℓv'
    Sq : Categoryᴰ (V ×C V) ℓsq ℓsq'
    Refl  : GlobalSection Sq
    Trans : Functorᴰ Id (_×pbᴰ_ {C = V}{D = V}{E = V} Sq Sq) Sq
    isPropSq : hasPropHoms Sq

-- TODO: non-thin would need IdL, IdR, Assoc
