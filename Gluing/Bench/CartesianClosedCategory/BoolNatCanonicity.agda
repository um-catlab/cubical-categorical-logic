{-# OPTIONS --lossy-unification #-}
module Gluing.Bench.CartesianClosedCategory.BoolNatCanonicity where

-- Canonicity for the free CCC over the Bool/Nat quiver: closed
-- programs over Church encodings evaluate by refl to the expected
-- natural number or boolean.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat hiding (isEven; isOdd; factorial)
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Base
open import Gluing.CartesianClosedCategory.BoolNatCanonicity.UncurriedElim
open import Gluing.Bench.Reference
open import Gluing.Bench.CartesianClosedCategory.Church

-- run a closed program by canonicity and read off the result
toℕ : E ⊤ (Nat N) → ℕ
toℕ t = canonNat (app decodeNat t)

toBool : E ⊤ (Bool' 𝔹) → Bool
toBool t = Iso.fun canonicity-bool (app decodeBool t)

-- the programs run by canonicity on numerals
runPower : ℕ → ℕ → ℕ
runPower a b = toℕ (app2 power (churchNumeral a) (churchNumeral b))

-- k² + 2ᵏ
runPolynomial : ℕ → ℕ
runPolynomial k = toℕ (app2 plus
  (app2 times (churchNumeral k) (churchNumeral k))
  (app2 power 2 (churchNumeral k)))

runPredecessor runFibonacci runFactorial runHalve runSumOfSquares : ℕ → ℕ
runPredecessor k = toℕ (app predecessor (churchNumeral k))
runFibonacci k = toℕ (app fibonacci (churchNumeral k))
runFactorial k = toℕ (app factorial (churchNumeral k))
runHalve k = toℕ (app halve (churchNumeral k))
runSumOfSquares k = toℕ (app sumOfSquares (churchNumeral k))

runIsEven runDivisibleBy6 : ℕ → Bool
runIsEven k = toBool (app isEven (churchNumeral k))
runDivisibleBy6 k =
  toBool (app2 divisibleBy6 (churchNumeral k) (churchNumeral k))

tests : List Test
tests =
  -- arithmetic
    test! (runPower 2 12 ≡ powℕ 2 12)
  ∷ test! (runPolynomial 10 ≡ polyℕ 10)
  -- iteration over pairs
  ∷ test! (runPredecessor 500 ≡ predℕ 500)
  ∷ test! (runFibonacci 15 ≡ fibℕ 15)
  ∷ test! (runFactorial 6 ≡ factℕ 6)
  -- booleans
  ∷ test! (runIsEven 5000 ≡ evenℕ 5000)
  ∷ test! (runDivisibleBy6 3000 ≡ div6ℕ 3000)
  -- mixed state and lists
  ∷ test! (runHalve 100 ≡ halfℕ 100)
  ∷ test! (runSumOfSquares 20 ≡ sumSquaresℕ 20)
  ∷ []
