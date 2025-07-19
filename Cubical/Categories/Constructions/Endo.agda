{-# OPTIONS --safe #-}
{-

  Given an object x ∈ C, the one-object category of endomorphisms of x

-}

module Cubical.Categories.Constructions.Endo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv hiding (fiber)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor


private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Functor

module _ (C : Category ℓC ℓC') (x : C .ob) where
  Endo : Category ℓ-zero ℓC'
  Endo .ob = Unit
  Endo .Hom[_,_] _ _ = C [ x , x ]
  Endo .id = C .id
  Endo ._⋆_ = C ._⋆_
  Endo .⋆IdL = ⋆IdL C
  Endo .⋆IdR = ⋆IdR C
  Endo .⋆Assoc = ⋆Assoc C
  Endo .isSetHom = isSetHom C

  π : Functor Endo C
  π .F-ob = λ _ → x
  π .F-hom = λ z → z
  π .F-id = refl
  π .F-seq _ _ = refl
