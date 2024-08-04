{-# OPTIONS --safe #-}
module Cubical.WildCat.Instances.FromCategory where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma using (ΣPathP)

open import Cubical.WildCat.Base
open import Cubical.WildCat.Product

open WildCat

private
  variable
    ℓ ℓ' : Level
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

