
module Cubical.Categories.Functors.Constant.More where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Compose
open import Cubical.Categories.Functors.Constant

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor

Constant-natural :
  {B : Category ℓB ℓB'}{C : Category ℓC ℓC'} (D : Category ℓD ℓD') (d : ob D)
  (F : Functor B C)
  → Constant B D d ≡ Constant C D d ∘F F
Constant-natural _ _ _ = Functor≡ (λ _ → refl) (λ _ → refl)
