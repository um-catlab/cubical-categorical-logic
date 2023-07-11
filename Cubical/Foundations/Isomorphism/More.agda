{-# OPTIONS --safe #-}
module Cubical.Foundations.Isomorphism.More where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

isoToIsIso : {f : A → B} → isIso f → Iso A B
isoToIsIso {f = f} fIsIso .Iso.fun = f
isoToIsIso fIsIso .Iso.inv = fIsIso .fst
isoToIsIso fIsIso .Iso.rightInv = fIsIso .snd .fst
isoToIsIso fIsIso .Iso.leftInv = fIsIso .snd .snd

isIsoToIsEquiv : {f : A → B} → isIso f → isEquiv f
isIsoToIsEquiv fIsIso = isoToIsEquiv (isoToIsIso fIsIso)
