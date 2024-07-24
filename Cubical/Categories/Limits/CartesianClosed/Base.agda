{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.CartesianClosed.Base where

open import Cubical.Categories.Category
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.Terminal

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

CartesianClosedCategory : (ℓ ℓ' : Level) → Set (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
CartesianClosedCategory ℓ ℓ' =
    Σ[ C ∈ Category ℓ ℓ' ]
    Σ[ _ ∈ Terminal C ]
    Σ[ bp ∈ BinProducts C ]
       Exponentials C bp
