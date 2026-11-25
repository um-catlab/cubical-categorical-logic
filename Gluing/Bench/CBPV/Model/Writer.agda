{-# OPTIONS --prop --lossy-unification #-}
module Gluing.Bench.CBPV.Model.Writer where

-- Canonicity for CBPV over writer theories: a circuit evaluator that
-- counts gate evaluations, a test harness that logs its results, and a
-- divisibility scanner that logs the automaton states.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.Structure
open import Cubical.Data.Bool
open import Cubical.Data.FinData using (Fin; toℕ; isSetFin)
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Mod using (_mod_)
open import Cubical.Data.Sigma
open import Cubical.Categories.Instances.WalkingArrow
  renaming (Vertex to Kind; l to 𝒱; r to 𝒞)
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.Instances.Nat
open import Cubical.Algebra.Monoid.Instances.List
open import Cubical.Algebra.Theory.Instances.Writer using (tell; WriterTheory)
open import Gluing.CBPV.Model.Concrete
open import Gluing.Bench.Reference
open import Gluing.Bench.CBPV.Model.Base
open import Agda.Builtin.Strict using (primForce)

-- the pseudo-random input bits of the circuit
inputBit : ℕ → Bool
inputBit i = odd (half (i · 7 + 3))

-- gates on (value, gate count)
negR : Bool × ℕ → Bool × ℕ
negR (b , n) = not b , suc n

conjR disjR : Bool × ℕ → Bool × ℕ → Bool × ℕ
conjR (false , n) _ = false , suc n
conjR (true , n) (b , m) = b , suc (n + m)
disjR (true , n) _ = true , suc n
disjR (false , n) (b , m) = b , suc (n + m)

-- reference: value and gate count of the depth-d circuit
-- alternating ∨/¬ and ∧/¬ layers over inputs from i
circuitValue : ℕ → ℕ → Bool × ℕ
circuitValue zero i = inputBit i , 0
circuitValue (suc d) i = node (odd d)
  where
  node : Bool → Bool × ℕ
  node true = disjR (negR (circuitValue d i)) (circuitValue d (i + pow2 d))
  node false = conjR (circuitValue d i) (negR (circuitValue d (i + pow2 d)))

module WriterSyntax (W : Monoid ℓ-zero) where
  open Syntax (WriterTheory W) public
  open WriterBoolModelSyntax W using (WriterCanonicity)

  -- log m, then continue
  emit : ∀ {A : Ob 𝒱} {B : Ob 𝒞} → ⟨ W ⟩ → Tm _ A B → Tm _ A B
  emit m M = [op] (tell m) λ _ → M

  run : Tm _ UnitTy FBoolTy → ⟨ W ⟩ × Bool
  run M = unlift (WriterCanonicity .Iso.inv M)

  -- the inputs of a depth-d circuit as nested binary sums
  In : ℕ → Ob 𝒱 → Ob 𝒱
  In zero X = D X
  In (suc d) X = In d (In d X)

  quoteIn : ∀ d {X : Ob 𝒱} → ℕ → Tm _ X (In d X)
  quoteIn zero i = tagB (inputBit i)
  quoteIn (suc d) i = seqS (quoteIn d (i + pow2 d)) (quoteIn d i)

  -- discard the inputs of a subcircuit
  skip : ∀ d {X : Ob 𝒱} → Tm _ (In d X) X
  skip zero = [+E] idS idS
  skip (suc d) = seqS (skip d) (skip d)

  module Evaluator (tick : ∀ {A : Ob 𝒱} {B : Ob 𝒞} → Tm _ A B → Tm _ A B)
    where
    negE : ∀ {Y X : Ob 𝒱} → Tm _ Y ([F] (D X)) → Tm _ Y ([F] (D X))
    negE e = e >>= [+E]
      (tick (return (tagB false)))
      (tick (return (tagB true)))

    conjE disjE : ∀ {Y Z X : Ob 𝒱}
      → Tm _ Y ([F] (D Z)) → Tm _ Z ([F] (D X)) → Tm _ Z X
      → Tm _ Y ([F] (D X))
    conjE e₁ e₂ s = e₁ >>= [+E]
      (tick e₂)
      (tick (return (seqS s (tagB false))))
    disjE e₁ e₂ s = e₁ >>= [+E]
      (tick (return (seqS s (tagB true))))
      (tick e₂)

    -- evaluate the circuit, short-circuiting ∧ and ∨ and
    -- calling tick at each gate
    eval : ∀ d {X : Ob 𝒱} → Tm _ (In d X) ([F] (D X))
    eval zero = [ret]
    eval (suc d) = node (odd d)
      where
      node : Bool → Tm _ (In (suc d) _) ([F] (D _))
      node true = disjE (negE (eval d)) (eval d) (skip d)
      node false = conjE (eval d) (negE (eval d)) (skip d)

    evalCircuit : ℕ → ℕ → Tm _ UnitTy FBoolTy
    evalCircuit d i = seqS (quoteIn d i) (eval d)

module Counting where
  open WriterSyntax NatMonoid public
  open Evaluator (emit 1) public

module Harness where
  open WriterSyntax (ListMonoid ((ℕ × Bool) , isSet× isSetℕ isSetBool)) public
  open Evaluator (λ M → M) public

  -- check a result against its expected value
  check : Bool → Tm _ BoolTy FBoolTy
  check true = [ret]
  check false = caseB λ r → return (tagB (not r))

  -- run each (depth, offset, expected) test, logging pass/fail
  runSuite : ℕ → List (ℕ × ℕ × Bool) → Bool → Tm _ UnitTy FBoolTy
  runSuite i [] ok = return (quoteBool ok)
  runSuite i ((e , o , b) ∷ ts) ok = evalCircuit e o >>= check b >>= caseB λ p →
    emit ((i , p) ∷ []) (runSuite (suc i) ts (ok and p))

  sampleSuite : ℕ → List (ℕ × ℕ × Bool)
  sampleSuite zero = []
  sampleSuite (suc m) = (m mod 4 , m · 5 , true) ∷ sampleSuite m

  -- reference for runSuite
  expectedLog : ℕ → List (ℕ × ℕ × Bool) → Bool → List (ℕ × Bool) × Bool
  expectedLog i [] ok = [] , ok
  expectedLog i ((e , o , b) ∷ ts) ok = entry (not (circuitValue e o .fst ⊕ b))
    where
    entry : Bool → List (ℕ × Bool) × Bool
    entry p = consFst (i , p) (expectedLog (suc i) ts (ok and p))

module Scanner (k : ℕ) where
  open WriterSyntax (ListMonoid (Fin (suc k) , isSetFin)) public
  open DFA k (λ q → emit (q ∷ [])) public

  runScan : ∀ n → Word Bool n → List ℕ × Bool
  runScan n bs = mapFst (map toℕ) (run (runAutomaton n bs))

  -- reference for runScan: the automaton states and result
  expectedTrace : ∀ n → ℕ → Word Bool n → List ℕ × Bool
  expectedTrace zero q bs = [] , (q ≡ᵇ 0)
  expectedTrace (suc n) q (b , bs) =
    primForce ((2 · q + bitℕ b) mod suc k) λ q' →
    consFst q' (expectedTrace n q' bs)

module Scan = Scanner 4

tests : List Test
tests =
  -- gate count and value of a depth-8 circuit
    test! (Counting.run (Counting.evalCircuit 8 0)
           ≡ (circuitValue 8 0 .snd , circuitValue 8 0 .fst))
  -- a 40-test suite with its log
  ∷ test! (Harness.run (Harness.runSuite 0 (Harness.sampleSuite 40) true)
           ≡ Harness.expectedLog 0 (Harness.sampleSuite 40) true)
  -- states of the mod-5 automaton on 64 bits
  ∷ test! (Scan.runScan 64 (patWord 64 0)
           ≡ Scan.expectedTrace 64 0 (patWord 64 0))
  ∷ []
