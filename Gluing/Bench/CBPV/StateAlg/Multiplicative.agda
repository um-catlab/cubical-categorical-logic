{-# OPTIONS --prop --lossy-unification #-}
module Gluing.Bench.CBPV.StateAlg.Multiplicative where

-- Canonicity for multiplicative CBPV with a boolean state cell: a long
-- sequence of calls to thunked procedures that set, clear and toggle
-- the cell, compared with the same sequence of functions on Bool.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Agda.Builtin.Nat using (mod-helper)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (Vertex to Kind; l to 𝒱; r to 𝒞)
open import
 Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.BoolState.Multiplicative
open import Gluing.CBPV.StateAlg.Multiplicative hiding (module CBPV)
open import Gluing.Bench.Reference using (Test; test; test!)
open CBPV BaseTy

U1 : Ob 𝒱
U1 = gen 𝟙
Unit! : Type
Unit! = Tm _ U1 ([F] U1)

infixr 5 _>>_
_>>_ : ∀ {B} → Unit! → Tm _ U1 B → Tm _ U1 B
M >> N = seqS M ([bind] N)

-- a procedure is a thunked computation
Proc : Type
Proc = Tm _ U1 ([U] ([F] U1))

call : Proc → Unit!
call f = seqS f [force]

-- the primitive procedures
toggleCell setCell clearCell : Proc
toggleCell = [thunk] ([rd] ([wt] false [ret]) ([wt] true [ret]))
setCell = [thunk] ([wt] true [ret])
clearCell = [thunk] ([wt] false [ret])

-- call f twice, or branch on the cell
twice : Proc → Proc
twice f = [thunk] (call f >> call f)

branch : Proc → Proc → Proc
branch f g = [thunk] ([rd] (call f) (call g))

-- a procedure exercising nested calls and branches
mixedRound : Proc
mixedRound = [thunk]
  ( call toggleCell
  >> call (branch (twice toggleCell) setCell)
  >> call (branch toggleCell clearCell)
  >> call (branch clearCell toggleCell))

readState : Tm _ U1 ([F] (gen BoolTy))
readState = [rd] (seqS tru [ret]) (seqS fls [ret])

-- references for the procedures as functions on Bool
refTwice : (Bool → Bool) → Bool → Bool
refTwice f s = f (f s)

refBranch : (Bool → Bool) → (Bool → Bool) → Bool → Bool
refBranch f g s = if s then f s else g s

refRound : Bool → Bool
refRound s =
  refBranch (λ _ → false) not
    (refBranch not (λ _ → false)
      (refBranch (refTwice not) (λ _ → true) (not s)))

-- the pseudo-random choice of the k-th procedure
callCode : ℕ → ℕ
callCode k = mod-helper 0 6 (k · k + 3 · k) 6

procedureFor : ℕ → Proc
procedureFor 1 = toggleCell
procedureFor 3 = setCell
procedureFor 5 = clearCell
procedureFor 6 = toggleCell
procedureFor _ = mixedRound

referenceFor : ℕ → Bool → Bool
referenceFor 1 = not
referenceFor 3 _ = true
referenceFor 5 _ = false
referenceFor 6 = not
referenceFor _ = refRound

-- call n procedures in sequence, then read the cell
callSequence : ℕ → ℕ → Tm _ U1 ([F] (gen BoolTy))
callSequence zero k = readState
callSequence (suc n) k =
  call (procedureFor (callCode k)) >> callSequence n (suc k)

-- reference for callSequence
referenceSequence : ℕ → ℕ → Bool → Bool
referenceSequence zero k s = s
referenceSequence (suc n) k s =
  referenceSequence n (suc k) (referenceFor (callCode k) s)

tests : List Test
tests =
  -- 500 calls starting from false
    test! (unquote-FBool (callSequence 500 0) false
           ≡ (referenceSequence 500 0 false , referenceSequence 500 0 false))
  ∷ []
