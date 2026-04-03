{-
  Arrow category and sub-category of Isos as categories displayed over C × C.

  Universal property: a section of the Arrow bundle is a natural
  transformation between functors, section of the Iso bundle is a
  natural isomorphism

-}
module Cubical.Categories.Displayed.Instances.Arrow.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Morphism
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Graph
open import Cubical.Categories.Displayed.Instances.PropertyOver
open import Cubical.Categories.Displayed.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Weaken.Base
open import Cubical.Categories.Displayed.Instances.Weaken.Properties
open import Cubical.Categories.Instances.TotalCategory hiding (Fst; Snd)
open import Cubical.Categories.Bifunctor hiding (Fst; Snd)

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

open Section
open Functor

module _ (C : Category ℓC ℓC') where
