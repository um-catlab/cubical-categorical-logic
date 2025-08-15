{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.WithFamilies.Simple.Instances.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
  renaming (SET to SETCat)
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Presheaf.CartesianLift

open import Cubical.Categories.WithFamilies.Simple.Instances.Democratic
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Displayed


open Category
open Categoryᴰ

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

-- TODO: level should be explicit in SETCC
SET : (ℓ : Level) → SCwF (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ
SET ℓ = CartesianCategory→SCwF (SETCC {ℓ})

SETⱽ : (ℓ ℓᴰ : Level) → SCwFⱽ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max ℓ ℓᴰ) (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max ℓ ℓᴰ)
SETⱽ ℓ ℓᴰ = CartesianCategoryⱽ→SCwFⱽ {C = SETCC} (SETᴰCartesianCategoryⱽ ℓ ℓᴰ)
