{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.CartesianClosed.Base where

open import Cubical.Categories.Exponentials
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant
open import Cubical.Data.Unit
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Constructions 
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Data.Sigma
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
private
    variable
        ℓ ℓ' : Level
    

CartesianClosedCategory : (ℓ ℓ' : Level) → Set (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
CartesianClosedCategory ℓ ℓ' = Σ[ C ∈ Category ℓ ℓ' ] Σ[ term ∈ Terminal C ] Σ[ prod ∈ BinProducts C ] Exponentials C prod
