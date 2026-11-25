{-# OPTIONS --prop --lossy-unification #-}
module Gluing.Bench.CBPV.Model.State.Base where

-- State syntax shared by the state benchmarks.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Categories.Instances.WalkingArrow
  renaming (Vertex to Kind; l to 𝒱; r to 𝒞)
open import Cubical.Algebra.Theory.Instances.State
  using (read; write; StateTheory)
open import Gluing.CBPV.Model.Concrete
open import Gluing.Bench.CBPV.Model.Base

module StateSyntax (Store : Type) (isSetStore : isSet Store) where
  open Syntax (StateTheory Store) public
  open StateBoolModelSyntax (Store , isSetStore) using (StateCanonicity)

  -- write the store
  put : ∀ {A : Ob 𝒱} → Store → Tm _ A ([F] A)
  put s = [op] (write s) λ _ → [ret]

  -- read the store into a value
  get : ∀ {A A' : Ob 𝒱} → (Store → Tm _ A A') → Tm _ A ([F] A')
  get q = [op] read λ s → return (q s)

  -- run a closed computation from an initial store
  run : Tm _ UnitTy FBoolTy → Store → Store × Bool
  run M s = unlift (StateCanonicity .Iso.inv M s)

