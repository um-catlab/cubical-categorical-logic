{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.BinProduct.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.BinProduct

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
  where

  open Functorᴰ
  private
    module D = Categoryᴰ D

  ΔCᴰ : Functorᴰ (Δ C) D (D ×Cᴰ D)
  ΔCᴰ .F-obᴰ xᴰ = xᴰ , xᴰ
  ΔCᴰ .F-homᴰ fᴰ = fᴰ , fᴰ
  ΔCᴰ .F-idᴰ = refl
  ΔCᴰ .F-seqᴰ fᴰ gᴰ = refl

  Δᴰ : Functorᴰ Id D (D ×ᴰ D)
  Δᴰ .F-obᴰ xᴰ = xᴰ , xᴰ
  Δᴰ .F-homᴰ fᴰ = fᴰ , fᴰ
  Δᴰ .F-idᴰ = refl
  Δᴰ .F-seqᴰ fᴰ gᴰ = refl
