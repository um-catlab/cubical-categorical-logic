{-# OPTIONS --safe #-}
module Cubical.Foundations.HLevels.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

private
  variable
    ℓ ℓ' : Level

isSetDep : {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isSetDep = isOfHLevelDep 2

isSet→isSetDep :
 {A : Type ℓ} {B : A → Type ℓ'} (h : (a : A) → isSet (B a)) → isSetDep {A = A} B
isSet→isSetDep = isOfHLevel→isOfHLevelDep 2
