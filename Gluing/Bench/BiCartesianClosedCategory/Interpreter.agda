{-# OPTIONS --lossy-unification #-}
module Gluing.Bench.BiCartesianClosedCategory.Interpreter where

-- Canonicity for the free BiCCC: an interpreter for arithmetic
-- expression trees over n-bit words, written by case analysis.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using ()
  renaming (if_then_else_ to ifᵇ_then_else_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _·_; _≡ᵇ_)
import Cubical.Data.Nat as Nat
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Gluing.Bench.Reference
open import Gluing.Bench.BiCartesianClosedCategory.Base
open import Gluing.Bench.BiCartesianClosedCategory.Circuits hiding (tests)
open import Gluing.Bench.BiCartesianClosedCategory.Arithmetic hiding (tests)

-- expression trees of depth d: a word, or an operator bit
-- with two subtrees (true is addition, false multiplication)
ExprTree : ℕ → ℕ → Ob
ExprTree n zero = Word n
ExprTree n (suc d) = Word n + (Bit × (ExprTree n d × ExprTree n d))

-- the interpreter
evaluateTree : ∀ n d → E (ExprTree n d) (Word n)
evaluateTree n zero = idₑ'
evaluateTree n (suc d) =
  [ idₑ'
  , letE (π₂' ⋆ₑ π₁' ⋆ₑ evaluateTree n d)
    (letE (π₁' ⋆ₑ π₂' ⋆ₑ π₂' ⋆ₑ evaluateTree n d)
    (if π₁' ⋆ₑ π₁' ⋆ₑ π₁' then apply2 (wordAdd n) v1 v0
      else apply2 (wordMultiply n) v1 v0))
  ]'

-- a pseudo-random tree generated from the seed s
sampleTree : ∀ n d → ℕ → E ⊤ (ExprTree n d)
sampleTree n zero s = quoteWord n (s Nat.+ 3)
sampleTree n (suc d) s =
  ifᵇ s ≡ᵇ 5 then quoteWord n 200 ⋆ₑ σ₁'
  else ⟨ quoteBit (odd (half s))
       , ⟨ sampleTree n d (2 · s Nat.+ 1)
         , sampleTree n d (2 · s Nat.+ 2) ⟩' ⟩' ⋆ₑ σ₂'

-- reference value of sampleTree d s on ℕ
sampleTreeValue : ℕ → ℕ → ℕ
sampleTreeValue zero s = s Nat.+ 3
sampleTreeValue (suc d) s =
  ifᵇ s ≡ᵇ 5 then 200
  else (ifᵇ odd (half s) then Nat._+_ else _·_)
         (sampleTreeValue d (2 · s Nat.+ 1)) (sampleTreeValue d (2 · s Nat.+ 2))

-- the interpreter run by canonicity on a sample tree
sampleTreeResult : ∀ n d → ℕ → ℕ
sampleTreeResult n d s =
  canonicalWord n (apply (evaluateTree n d) (sampleTree n d s))

tests : List Test
tests =
  -- a depth-3 tree over 4-bit words
    test! (sampleTreeResult 4 3 0 ≡ lowBits 4 (sampleTreeValue 3 0))
  ∷ []
