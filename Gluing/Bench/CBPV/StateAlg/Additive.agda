{-# OPTIONS --prop --lossy-unification #-}
module Gluing.Bench.CBPV.StateAlg.Additive where

-- Canonicity for additive CBPV with a boolean state cell: string and
-- word algorithms that keep their working bit in the state.
-- unquote-FBool M s is the final state and result of M from state s.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Categories.Instances.WalkingArrow
  renaming (Vertex to Kind; l to 𝒱; r to 𝒞)
open import
  Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.BoolState.Additive
open import Gluing.CBPV.StateAlg.Additive
open import Gluing.Bench.Reference
open CBPV BaseTy

-- a string of n bits as n nested binary sums
BitString : ℕ → Ob 𝒱
BitString zero = UnitTy
BitString (suc n) = BitString n [+] BitString n

infixl 5 _>>=_
-- sequencing and return
_>>=_ : ∀ {A A' : Ob 𝒱} {B : Ob 𝒞} → Tm _ A ([F] A') → Tm _ A' B → Tm _ A B
M >>= N = seqS M ([bind] N)

return : ∀ {A A' : Ob 𝒱} → Tm _ A A' → Tm _ A ([F] A')
return V = seqS V [ret]

-- return the state cell
readState : Tm _ UnitTy ([F] BoolTy)
readState = [rd] (return tru) (return fls)

-- flip the state cell
toggle : ∀ {A : Ob 𝒱} → Tm _ A ([F] A)
toggle = [rd] ([wt] false [ret]) ([wt] true [ret])

quoteBits : (bs : List Bool) → Tm _ UnitTy (BitString (length bs))
quoteBits [] = idS
quoteBits (true ∷ bs) = seqS (quoteBits bs) [+I1]
quoteBits (false ∷ bs) = seqS (quoteBits bs) [+I2]

toggleOnOne : ∀ {A : Ob 𝒱} → Tm _ (A [+] A) ([F] A)
toggleOnOne = [+E] toggle [ret]

-- parity of a string, accumulated in the state
parityFold : ∀ n → Tm _ (BitString n) ([F] BoolTy)
parityFold zero = readState
parityFold (suc n) = toggleOnOne >>= parityFold n

parity : (bs : List Bool) → Tm _ UnitTy ([F] BoolTy)
parity bs = seqS (quoteBits bs) (parityFold (length bs))

-- a value tagged with whether the previous bit was a one
WithFlag : Ob 𝒱 → Ob 𝒱
WithFlag A = A [+] A

found notFound : ∀ {A : Ob 𝒱} → Tm _ A ([F] (WithFlag A))
found = return [+I1]
notFound = return [+I2]

detectStep : ∀ {A : Ob 𝒱} → Tm _ (WithFlag (A [+] A)) ([F] (WithFlag A))
detectStep = [+E]
  ([+E] ([wt] true found) ([wt] false found))
  ([+E] ([rd] ([wt] true found) ([wt] true notFound)) ([wt] false notFound))

-- whether the string has two adjacent ones; the state
-- remembers the previous bit
detectFold : ∀ n → Tm _ (WithFlag (BitString n)) ([F] BoolTy)
detectFold zero = [+E] (return tru) (return fls)
detectFold (suc n) = detectStep >>= detectFold n

detectAdjacentOnes : (bs : List Bool) → Tm _ UnitTy ([F] BoolTy)
detectAdjacentOnes bs =
  [wt] false (seqS (seqS (quoteBits bs) [+I2]) (detectFold (length bs)))

-- two n-bit numbers as n pairs of bits, least significant first
BitPairs : ℕ → Ob 𝒱
BitPairs zero = UnitTy
BitPairs (suc n) = (BitPairs n [+] BitPairs n) [+] (BitPairs n [+] BitPairs n)

quotePairs : ∀ n → ℕ → ℕ → Tm _ UnitTy (BitPairs n)
quotePairs zero a b = idS
quotePairs (suc n) a b =
  seqS (seqS (quotePairs n (half a) (half b)) (tag (odd b))) (tag (odd a))
  where
  tag : ∀ {A : Ob 𝒱} → Bool → Tm _ A (A [+] A)
  tag true = [+I1]
  tag false = [+I2]

compareStep : ∀ {A : Ob 𝒱} → Tm _ ((A [+] A) [+] (A [+] A)) ([F] A)
compareStep =
  [+E] ([+E] [ret] ([wt] false [ret])) ([+E] ([wt] true [ret]) [ret])

-- a < b, with the state holding a < b on the bits so far
compareFold : ∀ n → Tm _ (BitPairs n) ([F] BoolTy)
compareFold zero = readState
compareFold (suc n) = compareStep >>= compareFold n

lessThan : ∀ n → ℕ → ℕ → Tm _ UnitTy ([F] BoolTy)
lessThan n a b = [wt] false (seqS (quotePairs n a b) (compareFold n))

carryStep : ∀ {A : Ob 𝒱} → Tm _ ((A [+] A) [+] (A [+] A)) ([F] A)
carryStep = [+E] ([+E] ([wt] true [ret]) [ret]) ([+E] [ret] ([wt] false [ret]))

-- the carry out of a + b, with the carry in the state
carryFold : ∀ n → Tm _ (BitPairs n) ([F] BoolTy)
carryFold zero = readState
carryFold (suc n) = carryStep >>= carryFold n

addOverflows : ∀ n → ℕ → ℕ → Tm _ UnitTy ([F] BoolTy)
addOverflows n a b = [wt] false (seqS (quotePairs n a b) (carryFold n))

-- reference for detectAdjacentOnes
hasAdjacentOnes : Bool → List Bool → Bool
hasAdjacentOnes prev [] = false
hasAdjacentOnes prev (true ∷ bs) = prev or hasAdjacentOnes true bs
hasAdjacentOnes prev (false ∷ bs) = hasAdjacentOnes false bs

tests : List Test
tests =
  -- parity of 512 pseudo-random bits
    test! (unquote-FBool (parity (pat 512)) true
           ≡ (xorAll true (pat 512) , xorAll true (pat 512)))
  -- two adjacent ones in 512 pseudo-random bits
  ∷ test! (unquote-FBool (detectAdjacentOnes (pat 512)) true .snd
           ≡ hasAdjacentOnes false (pat 512))
  -- 64-bit comparison and addition overflow
  ∷ test! (unquote-FBool (lessThan 64 12345678901 12345678900) true .snd
           ≡ (12345678901 <ᵇ 12345678900))
  ∷ test! (unquote-FBool (addOverflows 64 18446744073709551000 1000) true .snd
           ≡ (predℕ (pow2 64) <ᵇ 18446744073709551000 + 1000))
  ∷ []
