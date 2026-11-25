{-# OPTIONS --prop --lossy-unification #-}
module Gluing.Bench.CBPV.Model.State.Registers where

-- Canonicity for CBPV over a store of two w-bit registers a and b,
-- kept as w pairs of bits: fibonacci steps and a triangular-sum loop.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Instances.WalkingArrow
  renaming (Vertex to Kind; l to 𝒱; r to 𝒞)
open import Gluing.Bench.Reference
open import Gluing.Bench.CBPV.Model.Base
open import Gluing.Bench.CBPV.Model.State.Base
open import Agda.Builtin.Strict using (primForce)

module Registers (w : ℕ) where
  Regs = Word (Bool × Bool) w
  open StateSyntax Regs (isSetWord (isSet× isSetBool isSetBool) w) public
  open Pairs

  -- apply a digitwise operation to the registers, returning its carry
  alu : ∀ {A : Ob 𝒱} → Word (Bool × Bool → Bool → (Bool × Bool) × Bool) w
    → Bool → Tm _ A ([F] (D A))
  alu fs c = get (quoteNum w) >>= ripple w fs c >>= caseB λ c' →
    caseNum w put >>= return (tagB c')

  -- digitwise steps: (a, b) ↦ (b, a + b), a ↦ a + b,
  -- b ↦ b - 1, and a test for b = 0
  fibAdd addAB decB zeroB : Bool × Bool → Bool → (Bool × Bool) × Bool
  fibAdd (a , b) c = (b , (a ⊕ b) ⊕ c) , maj a b c
  addAB (a , b) c = ((a ⊕ b) ⊕ c , b) , maj a b c
  decB (a , b) c = (a , b ⊕ c) , c and not b
  zeroB (a , b) c = (a , b) , c and not b

  fibStep : ∀ {A : Ob 𝒱} → Tm _ A ([F] A)
  fibStep = alu (rep w fibAdd) false >>= caseB λ _ → [ret]

  fibIter : ℕ → Tm _ UnitTy ([F] UnitTy)
  fibIter zero = [ret]
  fibIter (suc k) = fibStep >>= fibIter k

  -- k fibonacci steps
  fibonacciSteps : ℕ → Tm _ UnitTy FBoolTy
  fibonacciSteps k = fibIter k >>= return tru

  -- add b + (b - 1) + … + 1 onto a
  addTriangular : ℕ → Tm _ UnitTy FBoolTy
  addTriangular zero = return fls
  addTriangular (suc fuel) = alu (rep w zeroB) true >>= caseB λ where
    true → return tru
    false → alu (rep w addAB) false >>= caseB λ _ →
      alu (rep w decB) true >>= caseB λ _ → addTriangular fuel

  -- the registers holding a and b
  regs : ∀ n → ℕ → ℕ → Word (Bool × Bool) n
  regs zero a b = tt
  regs (suc n) a b = (odd a , odd b) , regs n (half a) (half b)

  -- reference: the registers after k fibonacci steps from (a, b)
  fibFrom : ℕ → ℕ → ℕ → Regs
  fibFrom zero a b = regs w a b
  fibFrom (suc k) a b = primForce (a + b) (fibFrom k b)

  runFib : ℕ → ℕ → ℕ → Regs × Bool
  runFib k a b = run (fibonacciSteps k) (regs w a b)

  runTriangle : ℕ → ℕ → Regs × Bool
  runTriangle a b = run (addTriangular (suc b)) (regs w a b)

module R16 = Registers 16
module R64 = Registers 64

tests : List Test
tests =
  -- 16-bit registers
    test! (R16.runFib 6 0 1 ≡ (R16.fibFrom 6 0 1 , true))
  ∷ test! (R16.runTriangle 3 3 ≡ (R16.regs 16 (3 + 6) 0 , true))
  -- 64-bit registers near overflow
  ∷ test! (R64.runFib 2 (pow2 64 ∸ 3) (pow2 64 ∸ 5)
           ≡ (R64.fibFrom 2 (pow2 64 ∸ 3) (pow2 64 ∸ 5) , true))
  ∷ []
