{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.More

-- There are multiple definitions of terminal object in a displayed category:
-- 1. A terminal object in the total category, which is preserved by projection
-- 2. A terminal object in the *fiber* of an object

private
  variable
    ℓC ℓC' ℓD ℓD' ℓP : Level

open Category
open Categoryᴰ
open Functorᴰ

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where
  module D = Categoryᴰ D
  TerminalPresheafᴰ : (P : Presheaf C ℓP) → Presheafᴰ D P ℓ-zero
  TerminalPresheafᴰ P .F-obᴰ x x₁ = Unit , isSetUnit
  TerminalPresheafᴰ P .F-homᴰ = λ _ x _ → tt
  TerminalPresheafᴰ P .F-idᴰ i = λ x x₁ → tt
  TerminalPresheafᴰ P .F-seqᴰ fᴰ gᴰ i = λ x _ → tt

  -- Terminal object over a terminal object
  -- TODO: refactor using Constant Functorᴰ eventually
  TerminalᴰSpec : Presheafᴰ D (TerminalPresheaf {C = C}) ℓ-zero
  TerminalᴰSpec = TerminalPresheafᴰ _

  Terminalᴰ : (term : Terminal' C) → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD')
  Terminalᴰ term = UniversalElementᴰ _ TerminalᴰSpec term

  module _ (c : C .ob) where
    -- Terminal object of the fiber of a fixed object

    -- TODO: Is this equivalent to the more "obvious" definition that
    -- Fiber c have a terminal object?
    -- No.
    FibTerminalᴰSpec : Presheafᴰ D (C [-, c ]) ℓ-zero
    FibTerminalᴰSpec = TerminalPresheafᴰ _

    -- This says that for every morphism f : c' → c in C and
    -- d ∈ D.ob[ c' ] there is a unique lift to fᴰ : D [ f ][ d' , 1c ]
    -- In program logic terms this is the "trivial postcondition"
    FibTerminalᴰ : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD')
    FibTerminalᴰ = UniversalElementᴰ D FibTerminalᴰSpec (selfUnivElt C c)

    module FibTerminalᴰNotation (fibTermᴰ : FibTerminalᴰ) where
      open UniversalElementᴰ
      1ᴰ : D.ob[ c ]
      1ᴰ = fibTermᴰ .vertexᴰ

      !tᴰ : ∀ {c'}(f : C [ c' , c ]) (d' : D.ob[ c' ]) → D [ f ][ d' , 1ᴰ ]
      !tᴰ f d' = invIsEq (fibTermᴰ .universalᴰ) tt
