{-# OPTIONS --prop --lossy-unification #-}
module Gluing.Bench.CBPV.Model.State.Divisibility where

-- Canonicity for CBPV over a Fin (k + 1) store: the remainder of a bit
-- string modulo k + 1, held in the store.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.FinData using (Fin; zero; suc; toℕ; isSetFin)
open import Cubical.Data.Nat.Mod using (_mod_)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Categories.Instances.WalkingArrow
  renaming (Vertex to Kind; l to 𝒱; r to 𝒞)
open import Gluing.Bench.Reference
open import Gluing.Bench.CBPV.Model.Base
open import Gluing.Bench.CBPV.Model.State.Base

module Divisibility (k : ℕ) where
  open StateSyntax (Fin (suc k)) isSetFin public
  open Bits

  -- one automaton step per bit, on the remainder in the store
  scan : ∀ n → Tm _ (Num n UnitTy) ([F] UnitTy)
  scan zero = [ret]
  scan (suc n) = caseB λ b →
    get tagFin >>= caseFin (λ q → put (dbl k q b)) >>= scan n

  -- whether the remainder is zero
  accept : Tm _ UnitTy FBoolTy
  accept = get tagFin >>= caseFin λ where
    zero → return tru
    (suc q) → return fls

  remainderProgram : ∀ n → Word Bool n → Tm _ UnitTy FBoolTy
  remainderProgram n bs = seqS (quoteNum n bs) (scan n) >>= accept

  -- final remainder and divisibility
  runDiv : ∀ n → Word Bool n → ℕ × Bool
  runDiv n bs = mapFst toℕ (run (remainderProgram n bs) zero)

  -- reference remainder
  remainder : ∀ n → Word Bool n → ℕ
  remainder n bs = valMSB n 0 bs mod suc k

open Divisibility 6

tests : List Test
tests =
  -- remainder modulo 7 of 24 pseudo-random bits
    test! (runDiv 24 (patWord 24 0)
           ≡ (remainder 24 (patWord 24 0) , (remainder 24 (patWord 24 0) ≡ᵇ 0)))
  ∷ []
