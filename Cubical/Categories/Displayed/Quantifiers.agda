module Cubical.Categories.Displayed.Quantifiers where

open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Constructions.Slice as Slice
open import Cubical.Categories.Displayed.Constructions.TotalCategory as ∫ᴰ
open import Cubical.Categories.Displayed.Constructions.Weaken as Wk
open import Cubical.Categories.Displayed.Fibration.Base

-- The universal/pi and existential/weak sigma type are defined as
-- left and right adjoints to a "weakening" functor
--
-- Cᴰ(x × y) → Cᴰ x
--     |        |
-- x:C , y:C → x:C

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (bp : BinProducts C)
  -- This is an overly strong assumption for the construction, we only
  -- need pullbacks of π₁
  (isFibration : isFibration' Cᴰ)
  where
  open Notation C bp
  private
    bpF = (BinProductF' C bp)
    Cᴰ[a×b] = reindex Cᴰ bpF
    Cᴰ[a] = reindex Cᴰ (Fst C C)
    module Cᴰ = Categoryᴰ Cᴰ

  π₁Fᴰ : Functorᴰ bpF Cᴰ[a] (C /C Cᴰ)
  π₁Fᴰ = Slice.introF C Cᴰ
    (Fst C C)
    (Reindex.π Cᴰ (Fst C C))
    π₁Nat

  weakenⱽ : Functorⱽ {C = C ×C C} Cᴰ[a] Cᴰ[a×b]
  weakenⱽ = Reindex.introF _ (reindF' _ Eq.refl Eq.refl
    (CartesianLift'F Cᴰ isFibration ∘Fⱽᴰ π₁Fᴰ))

  UniversalQuantifier : ∀ {a b} (p : Cᴰ.ob[ a × b ]) → Type _
  UniversalQuantifier = RightAdjointAtⱽ weakenⱽ

  -- TODO: define Existential Quantifier/weak Sigma as LeftAdjoint
