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
import Cubical.Categories.Displayed.Presheaf.Constructions as Presheafᴰ
open import Cubical.Categories.Displayed.Presheaf.CartesianLift

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.WithFamilies.Simple.Displayed

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' ℓDᴰ ℓDᴰ' ℓSᴰ ℓSᴰ' : Level

module _ {C : SCwF ℓC ℓC' ℓT ℓT'}{D : SCwF ℓD ℓD' ℓS ℓS'}
         (F : PreFunctor C D) (Dᴰ : SCwFⱽ D ℓDᴰ ℓDᴰ' ℓSᴰ ℓSᴰ') where
  reindex : SCwFⱽ C ℓDᴰ ℓDᴰ' ℓSᴰ ℓSᴰ'
  reindex .fst = Categoryᴰ.reindex (Dᴰ .fst) (F .fst)
  reindex .snd .fst A = Dᴰ .snd .fst (F .snd .fst A)
  reindex .snd .snd .fst Aᴰ = Presheafᴰ.reindHet (F .snd .snd) (Dᴰ .snd .snd .fst Aᴰ)
  reindex .snd .snd .snd .fst = Categoryᴰ.TerminalsⱽReindex (Dᴰ .snd .snd .snd .fst)
  reindex .snd .snd .snd .snd .fst = Categoryᴰ.isFibrationReindex _ _ (Dᴰ .snd .snd .snd .snd .fst)
  reindex .snd .snd .snd .snd .snd .fst = Categoryᴰ.BinProductsⱽReindex (Dᴰ .snd .snd .snd .snd .snd .fst)
  reindex .snd .snd .snd .snd .snd .snd Aᴰ = isFibrationReindHet (F .snd .snd) (Dᴰ .snd .snd .snd .snd .snd .snd Aᴰ)
