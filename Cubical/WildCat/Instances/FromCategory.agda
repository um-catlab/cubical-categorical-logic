{-# OPTIONS --safe #-}
module Cubical.WildCat.Instances.FromCategory where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma using (ΣPathP)

open import Cubical.WildCat.Base
open import Cubical.Categories.Category.Base

open WildCat

private
  variable
    ℓ ℓ' : Level
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open Category
open WildCat
fromCat : Category ℓC ℓC' → WildCat ℓC ℓC'
fromCat C .ob = ob C
fromCat C .Hom[_,_] = C .Hom[_,_]
fromCat C .id = C .id
fromCat C ._⋆_ = C ._⋆_
fromCat C .⋆IdL = C .⋆IdL
fromCat C .⋆IdR = C .⋆IdR
fromCat C .⋆Assoc = C .⋆Assoc
