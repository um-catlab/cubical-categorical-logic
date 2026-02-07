{- A SCwFⱽ can be reindexed along a pre-Functor -}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.WithFamilies.Simple.Instances.Reindex where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Morphism.Alt

import Cubical.Categories.Displayed.Constructions.Reindex as Categoryᴰ
import Cubical.Categories.Displayed.Constructions.Reindex.CurriedFibration as Categoryᴰ
import Cubical.Categories.Displayed.Presheaf.Constructions as Presheafᴰ
open import Cubical.Categories.Displayed.Presheaf.CartesianLift
open import Cubical.Categories.Displayed.Presheaf.Base

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.WithFamilies.Simple.Displayed

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' ℓDᴰ ℓDᴰ' ℓSᴰ ℓSᴰ' : Level

module _ {C : SCwF ℓC ℓC' ℓT ℓT'}{D : SCwF ℓD ℓD' ℓS ℓS'}
         (F : PreFunctor C D) (Dᴰ : SCwFⱽ D ℓDᴰ ℓDᴰ' ℓSᴰ ℓSᴰ') where
  private module Dᴰ = SCwFⱽ Dᴰ
  reindex : SCwFⱽ C ℓDᴰ ℓDᴰ' ℓSᴰ ℓSᴰ'
  reindex .SCwFⱽ.Cᴰ = Categoryᴰ.reindex Dᴰ.Cᴰ (F .fst)
  reindex .SCwFⱽ.Tyᴰ A = Dᴰ.Tyᴰ (F .snd .fst A)
  reindex .SCwFⱽ.Tmᴰ Aᴰ = Presheafᴰ.reindHet (F .snd .snd) (Dᴰ.Tmᴰ Aᴰ)
  reindex .SCwFⱽ.terminalsⱽ = Categoryᴰ.TerminalsⱽReindex Dᴰ.terminalsⱽ
  reindex .SCwFⱽ.isFib = Categoryᴰ.isFibrationReindex _ Dᴰ.isFib
  reindex .SCwFⱽ.binProductsⱽ = Categoryᴰ.BinProductsⱽReindex Dᴰ.binProductsⱽ
  reindex .SCwFⱽ.TmᴰFib Aᴰ = isFibrationReindHet (F .snd .snd) (Dᴰ.TmᴰFib Aᴰ)
