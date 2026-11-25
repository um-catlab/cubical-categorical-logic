{-# OPTIONS --lossy-unification #-}
module Gluing.Bench.BiCartesianClosedCategory.Arithmetic where

-- Canonicity for the free BiCCC: word multiplication and an
-- overflow-checked sum returning an optional word.

open import Cubical.Foundations.Prelude
open import Agda.Builtin.FromNat
open import Cubical.Data.Bool using ()
  renaming (if_then_else_ to ifᵇ_then_else_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _·_; _<ᵇ_)
import Cubical.Data.Nat as Nat
open import Cubical.Data.List using (List; []; _∷_; foldr)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Gluing.BiCartesianClosedCategory.BoolNatCanonicity.Forded
open import Gluing.Bench.Reference
open import Gluing.Bench.BiCartesianClosedCategory.Base
open import Gluing.Bench.BiCartesianClosedCategory.Circuits hiding (tests)

open Section

-- the all-zero word
zeroWord : ∀ {Γ} n → E Γ (Word n)
zeroWord zero = !ₑ'
zeroWord (suc n) = ⟨ fls , zeroWord n ⟩'

-- drop the most significant bit
truncateWord : ∀ n → E (Word (suc n)) (Word n)
truncateWord zero = !ₑ'
truncateWord (suc n) = ⟨ π₁' , π₂' ⋆ₑ truncateWord n ⟩'

-- shift-and-add multiplication modulo 2ⁿ
wordMultiply : ∀ n → E (Word n × Word n) (Word n)
wordMultiply zero = !ₑ'
wordMultiply (suc n) =
  letE π₁' (letE (π₁' ⋆ₑ π₂')
  (letE (apply2 (wordMultiply n) (v1 ⋆ₑ π₂') (v0 ⋆ₑ truncateWord n))
  (apply2 (wordAdd (suc n))
    (if v2 ⋆ₑ π₁' then v1 else zeroWord (suc n)) ⟨ fls , v0 ⟩')))

-- an optional value
Option : Ob → Ob
Option A = ⊤ + A

-- add the list onto acc, returning nothing on overflow
checkedSum : ∀ {Γ} n → E Γ (Word n) → List ℕ → E Γ (Option (Word n))
checkedSum n acc [] = acc ⋆ₑ σ₂'
checkedSum n acc (x ∷ xs) =
  letE (⟨ ⟨ acc , quoteWord n x ⟩' , fls ⟩' ⋆ₑ rippleCarryAdder n)
  (if v0 ⋆ₑ π₂' then !ₑ' ⋆ₑ σ₁' else checkedSum n (v0 ⋆ₑ π₁') xs)

decodeOption : ∀ n {x} → S .F-obᴰ (Option (Word n)) x .fst → Maybe ℕ
decodeOption n (inl _) = nothing
decodeOption n (inr ((_ , r) , _)) = just (decodeWord n r)

-- run a closed optional word by canonicity
canonicalOption : ∀ n → E ⊤ (Option (Word n)) → Maybe ℕ
canonicalOption n t = decodeOption n (can t .fst .snd)

-- reference: the sum if it fits in n bits
refCheckedSum : ℕ → List ℕ → Maybe ℕ
refCheckedSum n xs = go (foldr Nat._+_ 0 xs)
  where
  go : ℕ → Maybe ℕ
  go s = ifᵇ s <ᵇ pow2 n then just s else nothing

-- the k inputs 7i + 3 for i < k
sampleInputs : ℕ → List ℕ
sampleInputs zero = []
sampleInputs (suc k) = (k · 7 Nat.+ 3) ∷ sampleInputs k

-- the programs run by canonicity on concrete inputs
wordProduct : ∀ n → ℕ → ℕ → ℕ
wordProduct n a b =
  canonicalWord n (apply2 (wordMultiply n) (quoteWord n a) (quoteWord n b))

checkedSumOf : ∀ n → List ℕ → Maybe ℕ
checkedSumOf n xs = canonicalOption n (checkedSum n (quoteWord n 0) xs)

tests : List Test
tests =
  -- 6-bit multiplication wraps modulo 2⁶
    test! (wordProduct 6 53 45 ≡ lowBits 6 (53 · 45))
  -- a checked sum that fits in 6 bits
  ∷ test! (checkedSumOf 6 (sampleInputs 3) ≡ refCheckedSum 6 (sampleInputs 3))
  ∷ []
