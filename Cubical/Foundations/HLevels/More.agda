module Cubical.Foundations.HLevels.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ ℓ' : Level

isPropIso : {A : Type ℓ}{B : Type ℓ'} → Iso A B → isProp B → isProp A
isPropIso f = isPropRetract (f .Iso.fun) (Iso.inv f) (Iso.ret f)

isSetIso : {A : Type ℓ}{B : Type ℓ'} → Iso A B → isSet B → isSet A
isSetIso f = isSetRetract (f .Iso.fun) (Iso.inv f) (Iso.ret f)

isSetDep : {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isSetDep = isOfHLevelDep 2

isSet→isSetDep :
 {A : Type ℓ} {B : A → Type ℓ'} (h : (a : A) → isSet (B a)) → isSetDep {A = A} B
isSet→isSetDep = isOfHLevel→isOfHLevelDep 2

isProp→isPropDep :
 {A : Type ℓ} {B : A → Type ℓ'} (h : (a : A) → isProp (B a)) → isPropDep {A = A} B
isProp→isPropDep = isOfHLevel→isOfHLevelDep 1
