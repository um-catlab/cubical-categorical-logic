{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Sets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More

private variable ℓ : Level

open UniversalElement
open Category

terminal'SET : Terminal' (SET ℓ)
terminal'SET .vertex = Unit* , isSetUnit*
terminal'SET .element = tt
terminal'SET .universal X .equiv-proof y = uniqueExists
  (λ _ → tt*)
  (isPropUnit tt tt)
  (λ _ p' q' → isSetUnit tt tt p' q')
  (λ _ _ → funExt λ _ → isPropUnit* tt* tt*)

module _ {ℓSET : Level} where
  BinProducts'SET : BinProducts' (SET ℓSET)
  BinProducts'SET (X , Y) .vertex = X .fst × Y .fst , isSet× (X .snd) (Y .snd)
  BinProducts'SET (X , Y) .element = fst , snd
  BinProducts'SET (X , Y) .universal Z .equiv-proof (f , g) =
    uniqueExists (λ z → f z , g z) refl
    (λ h → isSet×
      (SET ℓSET .isSetHom {x = Z} {y = X})
      (SET ℓSET .isSetHom {x = Z} {y = Y})
      ((λ z → (h z) .fst) , λ z → (h z) .snd) (f , g))
    λ h p i z → (sym p) i .fst z , (sym p) i .snd z

module _ {ℓSET : Level} where
  Exponentials'SET : Exponentials (SET ℓSET)
    (BinProducts'ToBinProducts  (SET ℓSET)  BinProducts'SET)
  Exponentials'SET (X , Y) .vertex =
    (SET ℓSET)[ Y , X ] , SET ℓSET .isSetHom {Y}{X}
  Exponentials'SET (X , Y) .element = λ{(Y→X , y) → Y→X y}
  Exponentials'SET (X , Y) .universal Z .equiv-proof f =
    uniqueExists (λ z y → f (z , y)) refl
      (λ a' → SET ℓSET .isSetHom {BinProducts'SET (Z , Y) .vertex} {X} _ _)
      (λ Z→Y→X p → funExt λ z → funExt λ y → funExt⁻ (sym p)  (z , y) )

module _ {ℓSET : Level} where
  SET'CCC : CartesianClosedCategory (ℓ-suc ℓSET) ℓSET
  SET'CCC = SET ℓSET ,
          (Terminal'ToTerminal terminal'SET) ,
          (BinProducts'ToBinProducts  (SET ℓSET)  BinProducts'SET) ,
          Exponentials'SET
