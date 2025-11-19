module Cubical.Categories.LocallySmall.Instances.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma.More
open import Cubical.Data.Unit

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Indiscrete

open Category
open Σω

UNIT : GloballySmallCategory (Liftω Unit) ℓ-zero
UNIT = Indiscrete (Liftω Unit)

SmallUNIT : SmallCategory ℓ-zero ℓ-zero
SmallUNIT = smallcat _ UNIT
