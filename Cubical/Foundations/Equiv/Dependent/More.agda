{-# OPTIONS --safe #-}
module Cubical.Foundations.Equiv.Dependent.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Dependent

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A : Type ℓ
    B : Type ℓ'
    P : A → Type ℓ''
    Q : B → Type ℓ'''
open Iso
open IsoOver
open isIsoOver

module _ {isom : Iso A B} {fun : mapOver (isom .fun) P Q} where
  isIsoOver→isIsoΣ :
    isIsoOver isom P Q fun
    → isIso {A = Σ A P}{B = Σ B Q} λ (a , p) → Iso.fun isom a , fun a p
  isIsoOver→isIsoΣ x .fst = λ z → inv isom (z .fst) , x .inv (z .fst) (z .snd)
  isIsoOver→isIsoΣ x .snd .fst b =
    ΣPathP ((rightInv isom (b .fst)) , (x .rightInv (b .fst) (b .snd)))
  isIsoOver→isIsoΣ x .snd .snd a =
    ΣPathP ((leftInv isom (a .fst)) , (x .leftInv (a .fst) (a .snd)))
