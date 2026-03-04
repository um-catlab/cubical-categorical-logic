{-# OPTIONS  --lossy-unification #-}
{-

  Alternate definition as a right adjoint. Turns out to be less nice than the one in Displayed.BinProduct

-}
module Cubical.Categories.Displayed.Limits.BinProduct.Adjoint where

open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.Adjoint
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Displayed.BinProduct as BP
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Instances.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Profunctor
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open UniversalElement
open UniversalElementᴰ
open UniversalElementⱽ
open isIsoOver

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓD ℓD') where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ

  BinProductᴰ : ∀ {c12} → BinProduct C c12
              → (Cᴰ.ob[ c12 .fst ] × Cᴰ.ob[ c12 .snd ])
              → Type _
  BinProductᴰ = RightAdjointAtᴰ (ΔCᴰ Cᴰ)

  BinProductᴰProf : ∀ {c12} → BinProduct C c12
              → Profunctorᴰ (RightAdjointProf (Δ C)) (Cᴰ BP.×Cᴰ Cᴰ) Cᴰ ℓD'
  BinProductᴰProf bp = RightAdjointProfᴰ (ΔCᴰ Cᴰ)

  BinProductⱽ : ∀ {c} → (Cᴰ.ob[ c ] × Cᴰ.ob[ c ]) → Type _
  BinProductⱽ = RightAdjointAtⱽ (Δᴰ Cᴰ)

  BinProductProfⱽ : Profunctorⱽ (Cᴰ BP.×ᴰ Cᴰ) Cᴰ ℓD'
  BinProductProfⱽ = RightAdjointProfⱽ (Δᴰ Cᴰ)
