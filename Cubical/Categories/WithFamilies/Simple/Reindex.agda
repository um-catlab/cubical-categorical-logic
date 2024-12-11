{-

  A displayed SCwF is an abstract notion of "logical family" over a SCwF

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.WithFamilies.Simple.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Constructions.TotalCategory.Limits
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.WithFamilies.Simple.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
import Cubical.Categories.Displayed.Presheaf.CartesianLift as Presheafᴰ

private
  variable
    ℓC ℓC' ℓT ℓT' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level

open UniversalElement
open UniversalElementᴰ
open isIsoOver
open Iso

