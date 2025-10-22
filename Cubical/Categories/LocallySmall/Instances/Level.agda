module Cubical.Categories.LocallySmall.Instances.Level where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Instances.Indiscrete

LEVEL  : GloballySmallCategory (Liftω Level) ℓ-zero
LEVEL  = Indiscrete (Liftω Level)
