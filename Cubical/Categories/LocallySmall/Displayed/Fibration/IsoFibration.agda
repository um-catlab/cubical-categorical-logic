module Cubical.Categories.LocallySmall.Displayed.Fibration.IsoFibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
open import Cubical.Categories.LocallySmall.Displayed.Category
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base

open Category
open Functorᴰ
open CatIso


module _
  {C : Category Cob CHom-ℓ}
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  where
  private
    module Cᴰ = CategoryᴰNotation Cᴰ

  record IsoLift {c c'}
    (cᴰ : Cᴰ.Ob[ c' ]) (f : CatIso C c c') : Typeω
    where
    field
      f*cᴰ : Cᴰ.Ob[ c ]
      f*cᴰIsoᴰ : CatIsoᴰ Cᴰ f f*cᴰ cᴰ

  record IsoLift' {c c'}
    (cᴰ : Cᴰ.Ob[ c ]) (f : CatIso C c c') : Typeω
    where
    field
      f*cᴰ : Cᴰ.Ob[ c' ]
      f*cᴰIsoᴰ : CatIsoᴰ Cᴰ f cᴰ f*cᴰ

  isIsoFibration : Typeω
  isIsoFibration = ∀ {c c'} (cᴰ : Cᴰ.Ob[ c' ]) (f : CatIso C c c')
    → IsoLift cᴰ f

  isIsoFibration' : Typeω
  isIsoFibration' = ∀ {c c'} (cᴰ : Cᴰ.Ob[ c ]) (f : CatIso C c c')
    → IsoLift' cᴰ f
