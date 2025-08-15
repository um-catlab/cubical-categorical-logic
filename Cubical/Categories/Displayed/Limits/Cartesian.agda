{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Properties
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Fibration.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

record CartesianCategoryᴰ (CC : CartesianCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  open CartesianCategory CC
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    termᴰ : Terminalᴰ Cᴰ term
    bpᴰ   : BinProductsᴰ Cᴰ bp

  module Cᴰ = Categoryᴰ Cᴰ

record CartesianCategoryⱽ (C : Category ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    termⱽ : Terminalsⱽ Cᴰ
    bpⱽ   : BinProductsⱽ Cᴰ
    cartesianLifts : isFibration Cᴰ

  module Cᴰ = Categoryᴰ Cᴰ

module _ {CC : CartesianCategory ℓC ℓC'}
         (CCᴰ : CartesianCategoryⱽ (CC .CartesianCategory.C) ℓCᴰ ℓCᴰ') where
  open CartesianCategory CC
  open TerminalNotation term
  open CartesianCategoryⱽ CCᴰ
  open CartesianCategoryᴰ hiding (Cᴰ)
  CartesianCategoryⱽ→CartesianCategoryᴰ : CartesianCategoryᴰ CC ℓCᴰ ℓCᴰ'
  CartesianCategoryⱽ→CartesianCategoryᴰ .CartesianCategoryᴰ.Cᴰ = Cᴰ
  CartesianCategoryⱽ→CartesianCategoryᴰ .termᴰ = Terminalⱽ→Terminalᴰ Cᴰ (termⱽ 𝟙)
  CartesianCategoryⱽ→CartesianCategoryᴰ .bpᴰ =
    BinProductsⱽ→BinProductsᴰ Cᴰ cartesianLifts bpⱽ bp
