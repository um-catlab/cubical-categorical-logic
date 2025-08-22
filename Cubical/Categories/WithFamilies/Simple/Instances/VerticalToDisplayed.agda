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
  SCwFⱽ→SCwFᴰ : SCwFᴰ C ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ'
  SCwFⱽ→SCwFᴰ .fst = Cᴰ .fst
  SCwFⱽ→SCwFᴰ .snd .fst = Cᴰ .snd .fst
  SCwFⱽ→SCwFᴰ .snd .snd .fst = Cᴰ .snd .snd .fst
  SCwFⱽ→SCwFᴰ .snd .snd .snd .fst = Terminalⱽ→Terminalᴰ _ (Cᴰ .snd .snd .snd .fst _)
  SCwFⱽ→SCwFᴰ .snd .snd .snd .snd {Γ}{A} Γᴰ Aᴰ =
    ×ⱽRepr+π*→×ᴰRepr _
      (CartesianLift→CartesianLift' _ _ (CatLift→YoLift (Cᴰ .snd .snd .snd .snd .fst _ _)))
      (CartesianLift→CartesianLift' _ _ (Cᴰ .snd .snd .snd .snd .snd .snd _ _))
      (Cᴰ .snd .snd .snd .snd .snd .fst _ _)
