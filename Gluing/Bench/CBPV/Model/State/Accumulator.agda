{-# OPTIONS --prop --lossy-unification #-}
module Gluing.Bench.CBPV.Model.State.Accumulator where

-- Canonicity for CBPV over a w-bit store: the sum and the maximum of a
-- list of v-bit inputs, with the accumulator in the store.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Categories.Instances.WalkingArrow
  renaming (Vertex to Kind; l to 𝒱; r to 𝒞)
open import Gluing.Bench.Reference
open import Gluing.Bench.CBPV.Model.Base
open import Gluing.Bench.CBPV.Model.State.Base

module Accumulator (w v : ℕ) where
  open StateSyntax (Word Bool w) (isSetWord isSetBool w) public
  open Bits

  -- a list of m v-bit numbers as nested sums
  Nums : ℕ → Ob 𝒱 → Ob 𝒱
  Nums zero A = A
  Nums (suc m) A = Num v (Nums m A)

  quoteNums : ∀ {A : Ob 𝒱} (xs : List ℕ) → Tm _ A (Nums (length xs) A)
  quoteNums [] = idS
  quoteNums (x ∷ xs) = seqS (quoteNums xs) (quoteNum v (bits v x))

  -- zero-extend a u-bit word to n bits
  widen : ∀ u n → Word Bool u → Word Bool n
  widen u zero x = tt
  widen zero (suc n) x = false , widen zero n x
  widen (suc u) (suc n) (b , x) = b , widen u n x

  -- digitwise steps of addition and comparison
  addBit lessBit : Bool → Bool → Bool → Bool × Bool
  addBit k a c = (a ⊕ k) ⊕ c , maj a k c
  lessBit k a l = a , (not a and k) or (l and not (a ⊕ k))

  -- add x to the store, or replace the store by x if larger
  sumStep maxStep : Word Bool v → ∀ {A : Ob 𝒱} → Tm _ A ([F] A)
  sumStep x =
    get (quoteNum w) >>= ripple w (mapWord w addBit (widen v w x)) false
    >>= caseB λ _ → caseNum w put
  maxStep x =
    get (quoteNum w) >>= ripple w (mapWord w lessBit (widen v w x)) false
    >>= [+E] (caseNum w λ _ → put (widen v w x)) (caseNum w put)

  fold : (Word Bool v → ∀ {A : Ob 𝒱} → Tm _ A ([F] A))
    → ∀ m → Tm _ (Nums m UnitTy) ([F] UnitTy)
  fold step zero = [ret]
  fold step (suc m) = caseNum v λ x → step x >>= fold step m

  -- fold step over the inputs
  accumulate : (Word Bool v → ∀ {A : Ob 𝒱} → Tm _ A ([F] A))
    → List ℕ → Tm _ UnitTy FBoolTy
  accumulate step xs =
    seqS (quoteNums xs) (fold step (length xs)) >>= return tru

  -- m pseudo-random v-bit inputs
  sampleInputs : ℕ → List ℕ
  sampleInputs zero = []
  sampleInputs (suc m) = lowBits v (m · 37 + 11) ∷ sampleInputs m

  runSum runMax : List ℕ → Word Bool w × Bool
  runSum xs = run (accumulate sumStep xs) (bits w 0)
  runMax xs = run (accumulate maxStep xs) (bits w 0)

open Accumulator 16 4

tests : List Test
tests =
  -- sum and maximum of 4 inputs, starting from 0
    test! (runSum (sampleInputs 4)
           ≡ (bits 16 (foldr _+_ 0 (sampleInputs 4)) , true))
  ∷ test! (runMax (sampleInputs 4)
           ≡ (bits 16 (foldr max 0 (sampleInputs 4)) , true))
  ∷ []
