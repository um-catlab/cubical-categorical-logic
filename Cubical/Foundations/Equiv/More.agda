module Cubical.Foundations.Equiv.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : A → Type ℓ'

explicitΠEquiv : ({x : A} → B x) ≃ ((x : A) → B x)
explicitΠEquiv = isoToEquiv explicitΠIso
  where
  explicitΠIso : Iso ({x : A} → B x) ((x : A) → B x)
  explicitΠIso .Iso.fun f x = f {x}
  explicitΠIso .Iso.inv f {x} = f x
  explicitΠIso .Iso.sec f = refl
  explicitΠIso .Iso.ret f = refl
