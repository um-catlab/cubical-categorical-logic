{-# OPTIONS --safe #-}
{-- This file contains some utilities for reasoning
 -- about the HLevels of morphisms in displayed categories.
 --}
module Cubical.Categories.Displayed.HLevels.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Reasoning as Reasoning

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (isPropHom : hasPropHoms Cᴰ) where
  open Category
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module RCᴰ = Reasoning Cᴰ

  propHomsFiller :
    ∀ {x y}{xᴰ yᴰ}
      {f g : C [ x , y ]}
      (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
      (p : f ≡ g)
      gᴰ
    → fᴰ Cᴰ.≡[ p ] gᴰ
  propHomsFiller fᴰ p gᴰ = toPathP (isPropHom _ _ _ _ _)
