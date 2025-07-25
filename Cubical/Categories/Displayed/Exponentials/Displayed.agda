{-# OPTIONS --safe --lossy-unification #-}
{-
  Displayed Exponentials
-}
module Cubical.Categories.Displayed.Exponentials.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Limits.BinProduct

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  Exponentialᴰ :
    ∀ {c d} {c×- : hasAllBinProductWith C c}
    cᴰ (dᴰ : Cᴰ.ob[ d ]) (cᴰ×ᴰ- : hasAllBinProductWithᴰ Cᴰ c×- cᴰ)
    → (c⇒d : Exponential' C c d c×-)
    → Type _
  Exponentialᴰ cᴰ dᴰ cᴰ×ᴰ- c⇒d = RightAdjointAtᴰ (a×-Fᴰ Cᴰ cᴰ×ᴰ-) c⇒d dᴰ

  -- TODO: ∫Exponentialᴰ
