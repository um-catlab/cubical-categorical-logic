module Cubical.Categories.LocallySmall.Instances.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More
  using (isSet→Square)
  renaming (rectify to TypeRectify)

open import Cubical.Data.Prod using (_×ω_; _,_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Displayed.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Indiscrete

open Category
open Categoryᴰ
open Σω

UNIT : GloballySmallCategory (Liftω Unit) ℓ-zero
UNIT = Indiscrete (Liftω Unit)

SmallUNIT : SmallCategory ℓ-zero ℓ-zero
SmallUNIT = _ , UNIT
