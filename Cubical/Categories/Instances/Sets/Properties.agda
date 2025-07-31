{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Instances.Sets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More

private variable ℓ : Level

open UniversalElement
open Category

TerminalSET : Terminal' (SET ℓ)
TerminalSET .vertex = Unit* , isSetUnit*
TerminalSET .element = tt
TerminalSET .universal X .equiv-proof y = uniqueExists
  (λ _ → tt*)
  (isPropUnit tt tt)
  (λ _ p' q' → isSetUnit tt tt p' q')
  (λ _ _ → funExt λ _ → isPropUnit* tt* tt*)

module _ {ℓSET : Level} where
  BinProductsSET : BinProducts (SET ℓSET)
  BinProductsSET (X , Y) .vertex = X .fst × Y .fst , isSet× (X .snd) (Y .snd)
  BinProductsSET (X , Y) .element = fst , snd
  BinProductsSET (X , Y) .universal Z .equiv-proof (f , g) =
    uniqueExists (λ z → f z , g z) refl
    (λ h → isSet×
      (SET ℓSET .isSetHom {x = Z} {y = X})
      (SET ℓSET .isSetHom {x = Z} {y = Y})
      ((λ z → (h z) .fst) , λ z → (h z) .snd) (f , g))
    λ h p i z → (sym p) i .fst z , (sym p) i .snd z

module _ {ℓSET : Level} where
  ExponentialsSET : AllExponentiable (SET ℓSET) (BinProductsSET)
  ExponentialsSET X Y .vertex = (SET ℓSET)[ X , Y ] , isSet→ (Y .snd)
  ExponentialsSET X Y .element (f , x) = f x
  ExponentialsSET X Y .universal Z = isIsoToIsEquiv
    ( (λ f x z → f (x , z))
    , (λ _ → refl)
    , λ _ → refl)

module _ {ℓSET : Level} where
  SETCC : CartesianCategory (ℓ-suc ℓSET) ℓSET
  SETCC .CartesianCategory.C = SET ℓSET
  SETCC .CartesianCategory.term = TerminalSET
  SETCC .CartesianCategory.bp = BinProductsSET

  SETCCC : CartesianClosedCategory (ℓ-suc ℓSET) ℓSET
  SETCCC .CartesianClosedCategory.CC = SETCC
  SETCCC .CartesianClosedCategory.exps = ExponentialsSET
