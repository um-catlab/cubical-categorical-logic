{-# OPTIONS --safe --lossy-unification #-}
{-
  Vertical Exponentials

  Vertical exponentials are a way to express as a UniversalElementⱽ that
  1. every fiber has exponentials
  2. they are preserved by cartesian lift
-}
module Cubical.Categories.Displayed.Exponentials.Vertical where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Fiberwise
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf
import Cubical.Categories.Displayed.Reasoning as Reasoning

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ {C : Category ℓC ℓC'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  -- These are overly strong assumptions. TODO: make them more minimal
  (bpⱽ : hasAllBinProductⱽ Cᴰ)
  (cLs : isFibration Cᴰ)
  where
  -- TODO: move this into FibrationNotation
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module R = Reasoning Cᴰ

    _*_ : ∀ {Γ a} → (f : C [ Γ , a ]) → (aᴰ : Cᴰ.ob[ a ])
      → Cᴰ.ob[ Γ ]
    f * aᴰ = cLs aᴰ f .CartesianLift.f*yᴰ

    πcL : ∀ {Γ a} → (f : C [ Γ , a ]) → (aᴰ : Cᴰ.ob[ a ])
      → Cᴰ [ f ][ f * aᴰ , aᴰ ]
    πcL f aᴰ = cLs aᴰ f .CartesianLift.π

  open AllBinProductⱽNotation bpⱽ
  open Functorᴰ
  open CartesianLift

  module _ {a} (aᴰ aᴰ' : Cᴰ.ob[ a ]) where
    Exponentialⱽ : Type _
    Exponentialⱽ = Σ[ aᴰ⇒aᴰ' ∈ Exponential' Cᴰ.v[ a ] aᴰ aᴰ' (λ aᴰ'' → BinProductⱽ→BinProductFiber Cᴰ (bpⱽ (aᴰ , aᴰ''))) ]
      ∀ {b} (f : C [ b , a ])
      → preservesExponential' (CartesianLiftF-fiber Cᴰ cLs f) (λ c → BinProductⱽ→BinProductFiber Cᴰ (bpⱽ (aᴰ , c)))
        (λ c' → cartesianLift-preserves-BinProductFiber Cᴰ cLs (bpⱽ _) f)
        (λ c → BinProductⱽ→BinProductFiber Cᴰ (bpⱽ _))
        aᴰ⇒aᴰ'
