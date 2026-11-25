{-# OPTIONS --lossy-unification #-}
module Gluing.Bench.BiCartesianClosedCategory.Circuits where

-- Canonicity for the free BiCCC: boolean circuits on n-bit words built
-- from case analysis on bits, run on large literals.

open import Cubical.Foundations.Prelude
open import Agda.Builtin.FromNat
open import Cubical.Data.Bool using (Bool; _⊕_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _·_; _<ᵇ_)
import Cubical.Data.Nat as Nat
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Gluing.Bench.Reference
open import Gluing.Bench.BiCartesianClosedCategory.Base

-- logic gates on bits
notG : E Bit Bit
notG = [ fls , tru ]'

andG orG xorG xnorG : E (Bit × Bit) Bit
andG = if π₁' then π₂' else fls
orG = if π₁' then tru else π₂'
xorG = if π₁' then π₂' ⋆ₑ notG else π₂'
xnorG = xorG ⋆ₑ notG

-- apply a two-input gate
gate : ∀ {Γ} → E (Bit × Bit) Bit → E Γ Bit → E Γ Bit → E Γ Bit
gate g a b = ⟨ a , b ⟩' ⋆ₑ g

-- full adder: (a, (b, carry in)) ↦ (sum, carry out)
fullAdder : E (Bit × (Bit × Bit)) (Bit × Bit)
fullAdder =
  letE π₁' (letE (π₁' ⋆ₑ π₂' ⋆ₑ π₁') (letE (π₁' ⋆ₑ π₁' ⋆ₑ π₂' ⋆ₑ π₂')
  (letE (gate xorG v2 v1)
  (letE (gate andG v3 v2)
  (letE (gate xorG v1 v2)
  (letE (gate andG v2 v3)
   ⟨ v1 , gate orG v2 v0 ⟩'))))))

-- n-bit ripple-carry adder: ((a, b), carry in) ↦ (sum, carry out)
rippleCarryAdder : ∀ n → E ((Word n × Word n) × Bit) (Word n × Bit)
rippleCarryAdder zero = ⟨ !ₑ' , π₂' ⟩'
rippleCarryAdder (suc n) =
  letE (⟨ π₁' ⋆ₑ π₁' ⋆ₑ π₁' , ⟨ π₁' ⋆ₑ π₂' ⋆ₑ π₁' , π₂' ⟩' ⟩' ⋆ₑ fullAdder)
  (letE (π₂' ⋆ₑ π₁')
  (letE (π₁' ⋆ₑ π₂' ⋆ₑ π₂')
  (letE (⟨ ⟨ π₁' ⋆ₑ π₁' ⋆ₑ π₁' ⋆ₑ π₁' ⋆ₑ π₁' ⋆ₑ π₂'
           , π₁' ⋆ₑ π₁' ⋆ₑ π₁' ⋆ₑ π₁' ⋆ₑ π₂' ⋆ₑ π₂' ⟩' , π₂' ⟩'
         ⋆ₑ rippleCarryAdder n)
   ⟨ ⟨ π₁' ⋆ₑ π₁' ⋆ₑ π₂' , π₂' ⋆ₑ π₁' ⟩' , π₂' ⋆ₑ π₂' ⟩')))

-- addition modulo 2ⁿ
wordAdd : ∀ n → E (Word n × Word n) (Word n)
wordAdd n = ⟨ idₑ' , fls ⟩' ⋆ₑ rippleCarryAdder n ⋆ₑ π₁'

-- comparison of n-bit words: (a < b, a = b)
wordCompare : ∀ n → E (Word n × Word n) (Bit × Bit)
wordCompare zero = ⟨ fls , tru ⟩'
wordCompare (suc n) =
  letE (⟨ π₁' ⋆ₑ π₂' , π₂' ⋆ₑ π₂' ⟩' ⋆ₑ wordCompare n)
  (letE (v0 ⋆ₑ π₁') (letE (v1 ⋆ₑ π₂')
  ⟨ (if v0 then gate andG (a0 ⋆ₑ notG) b0 else v1)
  , gate andG v0 (⟨ a0 , b0 ⟩' ⋆ₑ xnorG) ⟩'))
  where
  a0 b0 : E ((((Word (suc n) × Word (suc n)) × (Bit × Bit)) × Bit) × Bit) Bit
  a0 = π₁' ⋆ₑ π₁' ⋆ₑ π₁' ⋆ₑ π₁' ⋆ₑ π₁'
  b0 = π₁' ⋆ₑ π₁' ⋆ₑ π₁' ⋆ₑ π₂' ⋆ₑ π₁'

-- complete binary trees of bits of depth k
Tree : ℕ → Ob
Tree zero = Bit
Tree (suc k) = Tree k × Tree k

-- parity of the 2ᵏ leaves, xor-ing the two subtrees
parityTree : ∀ k → E (Tree k) Bit
parityTree zero = idₑ'
parityTree (suc k) = ⟨ π₁' ⋆ₑ parityTree k , π₂' ⋆ₑ parityTree k ⟩' ⋆ₑ xorG

-- pseudo-random leaf contents
leafBit : ℕ → Bool
leafBit i = odd (half (i · i Nat.+ 3 · i Nat.+ 7))

quoteTree : ∀ k → ℕ → E ⊤ (Tree k)
quoteTree zero o = quoteBit (leafBit o)
quoteTree (suc k) o = ⟨ quoteTree k o , quoteTree k (o Nat.+ pow2 k) ⟩'

-- reference parity of the leaves of quoteTree k o
treeParity : ℕ → ℕ → Bool
treeParity zero o = leafBit o
treeParity (suc k) o = treeParity k o ⊕ treeParity k (o Nat.+ pow2 k)

-- a < b on n-bit words
lessThan : ∀ n → E (Word n × Word n) Bit
lessThan n = wordCompare n ⋆ₑ π₁'

-- the circuits run by canonicity on concrete inputs
wordSum : ∀ n → ℕ → ℕ → ℕ
wordSum n a b =
  canonicalWord n (apply2 (wordAdd n) (quoteWord n a) (quoteWord n b))

wordLessThan : ∀ n → ℕ → ℕ → Bool
wordLessThan n a b =
  canonicalBit (apply2 (lessThan n) (quoteWord n a) (quoteWord n b))

leafParity : ℕ → Bool
leafParity k = canonicalBit (apply (parityTree k) (quoteTree k 0))

tests : List Test
tests =
  -- 32-bit addition wraps modulo 2³²
    test! (wordSum 32 4000000000 123456789
           ≡ lowBits 32 (4000000000 Nat.+ 123456789))
  -- comparison of 32-bit and 8-bit words
  ∷ test! (wordLessThan 32 3000000001 3000000000 ≡ (3000000001 <ᵇ 3000000000))
  ∷ test! (wordLessThan 8 200 201 ≡ (200 <ᵇ 201))
  -- parity of the 64 leaves of a depth-6 tree
  ∷ test! (leafParity 6 ≡ treeParity 6 0)
  ∷ []
