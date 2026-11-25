{-# OPTIONS --lossy-unification #-}
module Gluing.Bench.Lambda.Negative where

-- Canonicity for the simply typed λ-calculus with function and product types,
-- run on Church-encoded arithmetic, booleans and lists.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (isEven; isOdd; factorial)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Unit
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Agda.Builtin.FromNat
open import Gluing.Lambda.BoolNatCanonicity.Negative
open Lam[b,n]
open import Gluing.Bench.Reference

private variable
  Γ : Ctx
  A B C D X R : Ty

N 𝔹 : Ty
N = ↑ nat
𝔹 = ↑ bool

-- terms of type A in context Γ
T : Ctx → Ty → Type
T Γ A = Tm Γ (x: A)

-- de Bruijn variables: v0 is the innermost binder
v0 : T (Γ ,x: A) A
v0 = var
v1 : T ((Γ ,x: A) ,x: B) A
v1 = seqS wk var
v2 : T (((Γ ,x: A) ,x: B) ,x: C) A
v2 = seqS wk v1
v3 : T ((((Γ ,x: A) ,x: B) ,x: C) ,x: D) A
v3 = seqS wk v2
v5 : ∀ {F G} → T ((((((Γ ,x: A) ,x: B) ,x: C) ,x: D) ,x: F) ,x: G) A
v5 = seqS wk (seqS wk v3)

-- application and two-argument application
app : T Γ (A [⇒] B) → T Γ A → T Γ B
app = [APP]

app2 : T Γ (A [⇒] (B [⇒] C)) → T Γ A → T Γ B → T Γ C
app2 f a b = app (app f a) b

lam : T (Γ ,x: A) B → T Γ (A [⇒] B)
lam = [λ]

pair : T Γ A → T Γ B → T Γ (A [×] B)
pair = [⟨_,_⟩]

first : T Γ (A [×] B) → T Γ A
first p = seqS p [π₁]
second : T Γ (A [×] B) → T Γ B
second p = seqS p [π₂]

natSuc : T Γ (N [⇒] N)
natSuc = seqS [] [su]
natZero : T Γ N
natZero = seqS [] [ze]
boolTrue boolFalse : T Γ 𝔹
boolTrue = seqS [] [tr]
boolFalse = seqS [] [fl]

-- Church numerals: n is λ f x. fⁿ x
Nat : Ty → Ty
Nat A = (A [⇒] A) [⇒] (A [⇒] A)

-- applyTimes n f x is the term fⁿ x
applyTimes : ℕ → T Γ (A [⇒] A) → T Γ A → T Γ A
applyTimes zero f x = x
applyTimes (suc n) f x = app f (applyTimes n f x)

-- the Church numeral of n; numeral literals elaborate to this
churchNumeral : ℕ → T Γ (Nat A)
churchNumeral n = lam (lam (applyTimes n v1 v0))

instance
  numeral : Number (T Γ (Nat A))
  numeral .Number.Constraint _ = Unit
  numeral .Number.fromNat n = churchNumeral n

churchZero : T Γ (Nat A)
churchZero = lam (lam v0)

-- successor: λ n f x. f (n f x)
churchSuc : T Γ (Nat A [⇒] Nat A)
churchSuc = lam (lam (lam (app v1 (app2 v2 v1 v0))))

churchOne : T Γ (Nat A)
churchOne = app churchSuc churchZero

-- addition: λ m n f x. m f (n f x)
plus : T Γ (Nat A [⇒] (Nat A [⇒] Nat A))
plus = lam (lam (lam (lam (app2 v3 v1 (app2 v2 v1 v0)))))

-- multiplication: λ m n f. m (n f)
times : T Γ (Nat A [⇒] (Nat A [⇒] Nat A))
times = lam (lam (lam (app v2 (app v1 v0))))

-- exponentiation: λ m n. n m
power : T Γ (Nat A [⇒] (Nat (A [⇒] A) [⇒] Nat A))
power = lam (lam (app v0 v1))

-- decodes a Church numeral at the base type N via suc and zero
decodeNat : T Γ (Nat N [⇒] N)
decodeNat = lam (app2 v0 natSuc natZero)

-- pairs of numerals
NatPair : Ty → Ty
NatPair A = Nat A [×] Nat A

-- predecessor iterates (a, b) ↦ (b, b + 1) from (0, 0)
predStep : T Γ (NatPair A [⇒] NatPair A)
predStep = lam (pair (second v0) (app churchSuc (second v0)))

predecessor : T Γ (Nat (NatPair A) [⇒] Nat A)
predecessor = lam (first (app2 v0 predStep (pair churchZero churchZero)))

-- fibonacci iterates (a, b) ↦ (b, a + b) from (0, 1)
fibStep : T Γ (NatPair A [⇒] NatPair A)
fibStep = lam (pair (second v0) (app2 plus (first v0) (second v0)))

fibonacci : T Γ (Nat (NatPair A) [⇒] Nat A)
fibonacci = lam (first (app2 v0 fibStep (pair churchZero churchOne)))

-- factorial iterates (k, a) ↦ (k + 1, (k + 1) · a)
factStep : T Γ (NatPair A [⇒] NatPair A)
factStep = lam (pair (app churchSuc (first v0))
                     (app2 times (app churchSuc (first v0)) (second v0)))

factorial : T Γ (Nat (NatPair A) [⇒] Nat A)
factorial = lam (second (app2 v0 factStep (pair churchZero churchOne)))

-- Church booleans: true selects the first argument
Bool' : Ty → Ty
Bool' A = A [⇒] (A [⇒] A)

churchTrue churchFalse : T Γ (Bool' A)
churchTrue = lam (lam v1)
churchFalse = lam (lam v0)

-- boolean negation, conjunction and if-then-else
negate : T Γ (Bool' A [⇒] Bool' A)
negate = lam (lam (lam (app2 v2 v0 v1)))

both : T Γ (Bool' A [⇒] (Bool' A [⇒] Bool' A))
both = lam (lam (lam (lam (app2 v3 (app2 v2 v1 v0) v0))))

ifThenElse : T Γ (Bool' A [⇒] (A [⇒] (A [⇒] A)))
ifThenElse = lam (lam (lam (app2 v2 v1 v0)))

-- isEven n negates true n times
isEven : T Γ (Nat (Bool' A) [⇒] Bool' A)
isEven = lam (app2 v0 negate churchTrue)

-- decodes a Church boolean at the base type 𝔹
decodeBool : T Γ (Bool' 𝔹 [⇒] 𝔹)
decodeBool = lam (app2 v0 boolTrue boolFalse)

HalfState : Ty → Ty
HalfState A = Nat A [×] Bool' (Nat A)

-- halve iterates (h, odd) ↦ (if odd then h + 1 else h, not odd)
halfStep : T Γ (HalfState A [⇒] HalfState A)
halfStep = lam (pair
  (app2 (app ifThenElse (second v0)) (app churchSuc (first v0)) (first v0))
  (app negate (second v0)))

halve : T Γ (Nat (HalfState A) [⇒] Nat A)
halve = lam (first (app2 v0 halfStep (pair churchZero churchFalse)))

BoolTriple : Ty → Ty
BoolTriple A = Bool' A [×] (Bool' A [×] Bool' A)

rotate : T Γ (BoolTriple A [⇒] BoolTriple A)
rotate = lam (pair (second (second v0)) (pair (first v0) (first (second v0))))

-- n is divisible by 6 iff it is even and a 3-cycle
-- rotated n times from (true, false, false) is at true
divisibleBy6 : T Γ (Nat (Bool' A) [⇒] (Nat (BoolTriple A) [⇒] Bool' A))
divisibleBy6 = lam (lam (app2 both (app isEven v1)
  (first (app2 v0 rotate (pair churchTrue (pair churchFalse churchFalse))))))

-- Church lists: a list is its own right fold
List' : Ty → Ty → Ty
List' X R = (X [⇒] (R [⇒] R)) [⇒] (R [⇒] R)

nil : T Γ (List' X R)
nil = lam (lam v0)

cons : T Γ (X [⇒] (List' X R [⇒] List' X R))
cons = lam (lam (lam (lam (app2 v1 v3 (app2 v2 v1 v0)))))

-- map over a Church list
mapList : T Γ ((X [⇒] A) [⇒] (List' X R [⇒] List' A R))
mapList =
  lam (lam (lam (lam (app2 v2 (lam (lam (app2 v3 (app v5 v1) v0))) v0))))

-- sum of a list of numerals
sumList : T Γ (List' (Nat A) (Nat A) [⇒] Nat A)
sumList = lam (app2 v0 plus churchZero)

square : T Γ (Nat A [⇒] Nat A)
square = lam (app2 times v0 v0)

UpToState : Ty → Ty
UpToState A = Nat A [×] List' (Nat A) (Nat A)

-- upTo n is n, …, 1: iterates (k, l) ↦ (k + 1, (k + 1) ∷ l)
uptoStep : T Γ (UpToState A [⇒] UpToState A)
uptoStep = lam (pair (app churchSuc (first v0))
                     (app2 cons (app churchSuc (first v0)) (second v0)))

upTo : T Γ (Nat (UpToState A) [⇒] List' (Nat A) (Nat A))
upTo = lam (second (app2 v0 uptoStep (pair churchZero nil)))

-- sumOfSquares n is 1² + … + n²
sumOfSquares : T Γ (Nat (UpToState A) [⇒] Nat A)
sumOfSquares = lam (app sumList (app2 mapList square (app upTo v0)))

-- run a closed program by canonicity and read off the result
toℕ : T _ (Nat N) → ℕ
toℕ t = eval (app decodeNat t)

toBool : T _ (Bool' 𝔹) → Bool
toBool t = eval (app decodeBool t)

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
  ∷ test! (runPredecessor 250 ≡ predℕ 250)
  ∷ test! (runFibonacci 13 ≡ fibℕ 13)
  ∷ test! (runFactorial 6 ≡ factℕ 6)
  -- booleans
  ∷ test! (runIsEven 250 ≡ evenℕ 250)
  ∷ test! (runDivisibleBy6 150 ≡ div6ℕ 150)
  -- mixed state and lists
  ∷ test! (runHalve 100 ≡ halfℕ 100)
  ∷ test! (runSumOfSquares 15 ≡ sumSquaresℕ 15)
  ∷ []
