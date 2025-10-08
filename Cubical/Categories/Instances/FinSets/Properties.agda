module Cubical.Categories.Instances.FinSets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Data.Unit
open import Cubical.Data.FinSet

open import Cubical.Categories.Category renaming (pathToIso to catPathToIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

open Categoryᴰ
