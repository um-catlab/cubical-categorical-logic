module Gluing.Bench.Reference where

-- Reference implementations on ℕ and Bool that the benchmark results
-- are compared against, and the Test record.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (isEven; isOdd)
open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R
open import Agda.Builtin.Nat using (div-helper ; mod-helper)

fibℕ : ℕ → ℕ
fibℕ zero = 0
fibℕ (suc zero) = 1
fibℕ (suc (suc n)) = fibℕ n + fibℕ (suc n)

factℕ : ℕ → ℕ
factℕ zero = 1
factℕ (suc n) = suc n · factℕ n

powℕ : ℕ → ℕ → ℕ
powℕ b zero = 1
powℕ b (suc e) = b · powℕ b e

polyℕ : ℕ → ℕ
polyℕ n = n · n + powℕ 2 n

evenℕ : ℕ → Bool
evenℕ zero = true
evenℕ (suc n) = not (evenℕ n)

mod3ℕ : ℕ → ℕ
mod3ℕ zero = 0
mod3ℕ (suc n) with mod3ℕ n
... | 2 = 0
... | k = suc k

div6ℕ : ℕ → Bool
div6ℕ n with evenℕ n | mod3ℕ n
... | true | 0 = true
... | _ | _ = false

halfℕ : ℕ → ℕ
halfℕ zero = 0
halfℕ (suc zero) = 0
halfℕ (suc (suc n)) = suc (halfℕ n)

sumSquaresℕ : ℕ → ℕ
sumSquaresℕ zero = 0
sumSquaresℕ (suc n) = suc n · suc n + sumSquaresℕ n

-- halving and parity via the builtins, fast on large literals
half : ℕ → ℕ
half k = div-helper 0 1 k 1

odd : ℕ → Bool
odd k = mod-helper 0 1 k 1 ≡ᵇ 1

pow2 : ℕ → ℕ
pow2 zero = 1
pow2 (suc n) = 2 · pow2 n

-- parity of a list of bits, starting from s
xorAll : Bool → List Bool → Bool
xorAll s [] = s
xorAll s (b ∷ bs) = xorAll (s ⊕ b) bs

-- pat n is a fixed pseudo-random string of n bits
bitsOf : ℕ → ℕ → List Bool
bitsOf zero k = []
bitsOf (suc n) k = odd (half (k · 7 + 3)) ∷ bitsOf n (suc k)

pat : ℕ → List Bool
pat n = bitsOf n 0

-- lowBits n k is k modulo 2ⁿ
lowBits : ℕ → ℕ → ℕ
lowBits n k = mod-helper 0 (predℕ (pow2 n)) k (predℕ (pow2 n))

-- a test states lhs ≡ rhs and proves it by refl
record Test : Type₁ where
  constructor test
  field
    {X} : Type
    lhs rhs : X
    lhs≡rhs : lhs ≡ rhs

-- test! (lhs ≡ rhs) proves the equation by refl as its own definition
macro
  test! : R.Term → R.Term → R.TC Unit
  test! eq hole =
    makeAuxiliaryDef "test" eq (R.def (quote refl) [])
    >>= λ p → R.unify hole
      (R.con (quote test) (R.unknown v∷ R.unknown v∷ p v∷ []))
