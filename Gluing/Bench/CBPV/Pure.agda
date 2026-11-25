{-# OPTIONS --prop --lossy-unification #-}
module Gluing.Bench.CBPV.Pure where

-- Canonicity for pure additive CBPV: the parity of a bit string,
-- computed by a value-level fold over nested sums.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (Vertex to Kind; l to 𝒱; r to 𝒞)
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.Pure.Additive
open import Gluing.CBPV.Pure.Additive
open import Gluing.Bench.Reference
open EZ-Can
open CBPV BaseTy
open Terms FUN

isInl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ⊎ B → Bool
isInl (inl _) = true
isInl (inr _) = false

-- run a closed computation by canonicity
runBool : Tm _ [1] ([F] BoolTy) → Bool
runBool M = isInl (AllCanonical (_ , M))

-- a string of n bits as n nested binary sums
BitString : ℕ → Ob 𝒱
BitString zero = [1]
BitString (suc n) = BitString n [+] BitString n

-- the value of a list of bits
quoteBits : (bs : List Bool) → Tm _ [1] (BitString (length bs))
quoteBits [] = idS
quoteBits (true ∷ bs) = seqS (quoteBits bs) [+I1]
quoteBits (false ∷ bs) = seqS (quoteBits bs) [+I2]

-- a value tagged with the running parity
WithFlag : Ob 𝒱 → Ob 𝒱
WithFlag A = A [+] A

-- consume one bit, flipping the flag on a one
parityStep : ∀ {A : Ob 𝒱} → Tm _ (WithFlag (A [+] A)) (WithFlag A)
parityStep = [+E] ([+E] [+I2] [+I1]) ([+E] [+I1] [+I2])

parityFold : ∀ n → Tm _ (WithFlag (BitString n)) (WithFlag [1])
parityFold zero = idS
parityFold (suc n) = seqS parityStep (parityFold n)

-- the parity of bs
parity : (bs : List Bool) → Tm _ [1] ([F] BoolTy)
parity bs =
  seqS (seqS (seqS (quoteBits bs) [+I2]) (parityFold (length bs))) [ret]

tests : List Test
tests =
  -- parity of 2000 pseudo-random bits
    test! (runBool (parity (pat 2000)) ≡ xorAll false (pat 2000))
  ∷ []
