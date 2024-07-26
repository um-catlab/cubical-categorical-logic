{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Indiscrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Categories.Category.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

open Category
Indiscrete : Type ℓC → Category ℓC ℓ-zero
Indiscrete X .ob = X
Indiscrete X .Hom[_,_] _ _ = Unit
Indiscrete X .id = tt
Indiscrete X ._⋆_ = λ f g → tt
Indiscrete X .⋆IdL _ = refl
Indiscrete X .⋆IdR _ = refl
Indiscrete X .⋆Assoc _ _ _ = refl
Indiscrete X .isSetHom = isSetUnit
