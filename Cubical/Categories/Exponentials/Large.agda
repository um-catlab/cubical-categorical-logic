-- NOTE : The implementation of Exponentials at Exponentials.Small is preferred

module Cubical.Categories.Exponentials.Large where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Constructions hiding (π₁; π₂)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
    C D : Category ℓC ℓC'

open Category

module _ (C : Category ℓC ℓC') where
  Exponential : (c d : C .ob) → Type _
  Exponential c d = UniversalElement C ((C [-, c ]) ⇒PshLarge (C [-, d ]))

  Exponentiable : ∀ c → Type _
  Exponentiable c = ∀ d → Exponential c d
