module Cubical.Categories.Instances.Sets.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Instances.BinProduct.Cartesian
  renaming (_×_ to _×CC_)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Sets.Properties

×SetsCF : ∀ {ℓ} → CartesianFunctor (SETCC {ℓ} ×CC SETCC {ℓ}) (SET ℓ)
×SetsCF .fst = ×Sets
×SetsCF .snd c c' Γ =
  isoToIsEquiv
    (iso
      (λ h →
        (λ z → h z .fst .fst , h z .snd .fst) ,
        (λ z → h z .fst .snd , h z .snd .snd))
      (λ h z →
        (h .fst z .fst , h .snd z .fst) ,
        (h .fst z .snd , h .snd z .snd))
      (λ _ → refl)
      (λ _ → refl))
