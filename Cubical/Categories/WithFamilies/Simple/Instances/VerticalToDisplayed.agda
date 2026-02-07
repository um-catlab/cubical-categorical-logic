{- A SCwFⱽ can be reindexed along a pre-Functor -}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.WithFamilies.Simple.Instances.VerticalToDisplayed where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

import Cubical.Categories.Displayed.Presheaf.Constructions as Presheafᴰ
open import Cubical.Categories.Displayed.Presheaf.CartesianLift
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct.Properties

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.WithFamilies.Simple.Displayed

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level

module _ {C : SCwF ℓC ℓC' ℓT ℓT'} {Cᴰ : SCwFⱽ C ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ'} where
  open SCwFⱽ Cᴰ renaming (Cᴰ to theCᴰ; Tyᴰ to theTyᴰ; Tmᴰ to theTmᴰ)
  SCwFⱽ→SCwFᴰ : SCwFᴰ C ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ'
  SCwFⱽ→SCwFᴰ .SCwFᴰ.Cᴰ = theCᴰ
  SCwFⱽ→SCwFᴰ .SCwFᴰ.Tyᴰ = theTyᴰ
  SCwFⱽ→SCwFᴰ .SCwFᴰ.Tmᴰ = theTmᴰ
  SCwFⱽ→SCwFᴰ .SCwFᴰ.termᴰ = Terminalⱽ→Terminalᴰ _ (terminalsⱽ _)
  SCwFⱽ→SCwFᴰ .SCwFᴰ.comprehensionᴰ Aᴰ Γᴰ =
    ×ⱽRepr+π*→×ᴰRepr _
      (isFib _ _)
      (TmᴰFib _ _)
      (binProductsⱽ _ _)
