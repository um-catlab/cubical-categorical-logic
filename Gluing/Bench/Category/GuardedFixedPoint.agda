{-# OPTIONS --lossy-unification #-}
module Gluing.Bench.Category.GuardedFixedPoint where

-- Guarded canonicity for the free category with delays and fixed
-- points: looping programs are run with a fuel bound and observed as
-- the number of steps taken and the result, if any.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Categories.Instances.Free.Category.GuardedFixedPoint
open import Cubical.Categories.Instances.ωSet hiding (next)
open import Gluing.Category.GuardedFixedPoint
open import Gluing.Bench.Reference using (Test; test; test!)
open Delayᴰ {V = Bool} quoteBool (_⋆ₑ [δ]) (λ M → ωUnit* {ℓ = ℓ-zero})

observe : ∀ {x n} → |Delayᴰ| x n → ℕ × Maybe Bool
observe (terminates {v = v} _) = 0 , just v
observe timeout = 0 , nothing
observe (steps d) = suc (observe d .fst) , observe d .snd

-- run a program with the given fuel
run : Exp [1] [RetBool] → ℕ → ℕ × Maybe Bool
run M n = observe (GuardedCanonicityFib M n .fst .snd)

-- k delay steps
pause : ∀ {B} → ℕ → Exp B B
pause zero = idₑ
pause (suc k) = pause k ⋆ₑ [δ]

-- a fixed point that unfolds once
loop : Exp [1] [RetBool] → Exp [1] [RetBool]
loop M = [fix] ([]ₑ ⋆ₑ M)

-- k nested loops each pausing j steps, then true
countdownLoop : ℕ → ℕ → Exp [1] [RetBool]
countdownLoop zero j = quoteBool true
countdownLoop (suc k) j = loop (countdownLoop k j ⋆ₑ pause j)

-- a loop that never returns
divergent : ℕ → Exp [1] [RetBool]
divergent zero = [fix] (pause 3)
divergent (suc k) = loop (divergent k ⋆ₑ pause 2)

-- nested loops pausing 1 and 2 steps, then false
alternatingLoop : ℕ → Exp [1] [RetBool]
alternatingLoop zero = quoteBool false
alternatingLoop (suc k) = loop (alternatingLoop k ⋆ₑ pause 1) ⋆ₑ pause 2

-- reference: s steps and then b, if s ≤ fuel
finishesWithin : ℕ → Bool → ℕ → ℕ × Maybe Bool
finishesWithin s b fuel =
  if s <ᵇ suc fuel then (s , just b) else (fuel , nothing)

-- reference: the fuel is exhausted
timesOut : ℕ → ℕ × Maybe Bool
timesOut fuel = fuel , nothing

tests : List Test
tests =
  -- 800 steps finish with exactly enough fuel, not with one less
    test! (run (countdownLoop 400 2) 800 ≡ finishesWithin (400 · 2) true 800)
  ∷ test! (run (countdownLoop 400 2) 799 ≡ finishesWithin (400 · 2) true 799)
  -- divergence uses up the fuel
  ∷ test! (run (divergent 200) 600 ≡ timesOut 600)
  -- 600 steps of alternating pauses
  ∷ test! (run (alternatingLoop 200) 600 ≡ finishesWithin (200 · 3) false 600)
  ∷ []
