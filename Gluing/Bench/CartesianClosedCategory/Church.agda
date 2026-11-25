{-# OPTIONS --lossy-unification #-}
module Gluing.Bench.CartesianClosedCategory.Church where

-- Church-encoded programs in the free CCC over the Bool/Nat quiver,
-- shared by the canonicity and NbE benchmarks.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (isEven; isOdd; factorial)
open import Cubical.Data.Unit
open import Agda.Builtin.FromNat
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Base
open import Gluing.CartesianClosedCategory.BoolNatCanonicity.UncurriedElim

Ty = ×⇒Quiver.obExpr ×⇒QUIVER
E = Expr ×⇒QUIVER

private variable
  Γ : Ty
  A B C D X R : Ty

N 𝔹 : Ty
N = ↑ nat
𝔹 = ↑ bool

-- de Bruijn variables: v0 is the innermost binder
v0 : E (Γ × A) A
v0 = π₂
v1 : E ((Γ × A) × B) A
v1 = π₁ ⋆ₑ π₂
v2 : E (((Γ × A) × B) × C) A
v2 = π₁ ⋆ₑ (π₁ ⋆ₑ π₂)
v3 : E ((((Γ × A) × B) × C) × D) A
v3 = π₁ ⋆ₑ (π₁ ⋆ₑ (π₁ ⋆ₑ π₂))
v5 : ∀ {F G} → E ((((((Γ × A) × B) × C) × D) × F) × G) A
v5 = π₁ ⋆ₑ (π₁ ⋆ₑ v3)

-- application and two-argument application
app : E Γ (A ⇒ B) → E Γ A → E Γ B
app f a = ⟨ f , a ⟩ ⋆ₑ eval

app2 : E Γ (A ⇒ (B ⇒ C)) → E Γ A → E Γ B → E Γ C
app2 f a b = app (app f a) b

-- projections out of a pair
first : E Γ (A × B) → E Γ A
first p = p ⋆ₑ π₁
second : E Γ (A × B) → E Γ B
second p = p ⋆ₑ π₂

-- the generators of the base types N and 𝔹 as terms
natSuc : E Γ (N ⇒ N)
natSuc = λ- (π₂ ⋆ₑ [su])
natZero : E Γ N
natZero = !ₑ ⋆ₑ [ze]
boolTrue boolFalse : E Γ 𝔹
boolTrue = !ₑ ⋆ₑ [t]
boolFalse = !ₑ ⋆ₑ [f]

-- Church numerals: n is λ f x. fⁿ x
Nat : Ty → Ty
Nat A = (A ⇒ A) ⇒ (A ⇒ A)

-- applyTimes n f x is the term fⁿ x
applyTimes : ℕ → E Γ (A ⇒ A) → E Γ A → E Γ A
applyTimes zero f x = x
applyTimes (suc n) f x = app f (applyTimes n f x)

-- the Church numeral of n; numeral literals elaborate to this
churchNumeral : ℕ → E Γ (Nat A)
churchNumeral n = λ- (λ- (applyTimes n v1 v0))

instance
  numeral : Number (E Γ (Nat A))
  numeral .Number.Constraint _ = Unit
  numeral .Number.fromNat n = churchNumeral n

churchZero : E Γ (Nat A)
churchZero = λ- (λ- v0)

-- successor: λ n f x. f (n f x)
churchSuc : E Γ (Nat A ⇒ Nat A)
churchSuc = λ- (λ- (λ- (app v1 (app2 v2 v1 v0))))

churchOne : E Γ (Nat A)
churchOne = app churchSuc churchZero

-- addition: λ m n f x. m f (n f x)
plus : E Γ (Nat A ⇒ (Nat A ⇒ Nat A))
plus = λ- (λ- (λ- (λ- (app2 v3 v1 (app2 v2 v1 v0)))))

-- multiplication: λ m n f. m (n f)
times : E Γ (Nat A ⇒ (Nat A ⇒ Nat A))
times = λ- (λ- (λ- (app v2 (app v1 v0))))

-- exponentiation: λ m n. n m
power : E Γ (Nat A ⇒ (Nat (A ⇒ A) ⇒ Nat A))
power = λ- (λ- (app v0 v1))

-- decodes a Church numeral at the base type N via suc and zero
decodeNat : E Γ (Nat N ⇒ N)
decodeNat = λ- (app2 v0 natSuc natZero)

NatPair : Ty → Ty
NatPair A = Nat A × Nat A

-- predecessor iterates (a, b) ↦ (b, b + 1) n times from (0, 0)
predStep : E Γ (NatPair A ⇒ NatPair A)
predStep = λ- ⟨ second v0 , app churchSuc (second v0) ⟩

predecessor : E Γ (Nat (NatPair A) ⇒ Nat A)
predecessor = λ- (first (app2 v0 predStep ⟨ churchZero , churchZero ⟩))

-- fibonacci iterates (a, b) ↦ (b, a + b) n times from (0, 1)
fibStep : E Γ (NatPair A ⇒ NatPair A)
fibStep = λ- ⟨ second v0 , app2 plus (first v0) (second v0) ⟩

fibonacci : E Γ (Nat (NatPair A) ⇒ Nat A)
fibonacci = λ- (first (app2 v0 fibStep ⟨ churchZero , churchOne ⟩))

-- factorial iterates (k, a) ↦ (k + 1, (k + 1) · a) from (0, 1)
factStep : E Γ (NatPair A ⇒ NatPair A)
factStep = λ- ⟨ app churchSuc (first v0)
              , app2 times (app churchSuc (first v0)) (second v0) ⟩

factorial : E Γ (Nat (NatPair A) ⇒ Nat A)
factorial = λ- (second (app2 v0 factStep ⟨ churchZero , churchOne ⟩))

-- Church booleans: true selects the first argument
Bool' : Ty → Ty
Bool' A = A ⇒ (A ⇒ A)

churchTrue churchFalse : E Γ (Bool' A)
churchTrue = λ- (λ- v1)
churchFalse = λ- (λ- v0)

-- boolean negation, conjunction and if-then-else
negate : E Γ (Bool' A ⇒ Bool' A)
negate = λ- (λ- (λ- (app2 v2 v0 v1)))

both : E Γ (Bool' A ⇒ (Bool' A ⇒ Bool' A))
both = λ- (λ- (λ- (λ- (app2 v3 (app2 v2 v1 v0) v0))))

ifThenElse : E Γ (Bool' A ⇒ (A ⇒ (A ⇒ A)))
ifThenElse = λ- (λ- (λ- (app2 v2 v1 v0)))

-- isEven n negates true n times
isEven : E Γ (Nat (Bool' A) ⇒ Bool' A)
isEven = λ- (app2 v0 negate churchTrue)

-- decodes a Church boolean at the base type 𝔹
decodeBool : E Γ (Bool' 𝔹 ⇒ 𝔹)
decodeBool = λ- (app2 v0 boolTrue boolFalse)

HalfState : Ty → Ty
HalfState A = Nat A × Bool' (Nat A)

-- halve iterates (h, odd) ↦ (if odd then h + 1 else h, not odd)
halfStep : E Γ (HalfState A ⇒ HalfState A)
halfStep =
  λ- ⟨ app2 (app ifThenElse (second v0)) (app churchSuc (first v0)) (first v0)
              , app negate (second v0) ⟩

halve : E Γ (Nat (HalfState A) ⇒ Nat A)
halve = λ- (first (app2 v0 halfStep ⟨ churchZero , churchFalse ⟩))

-- n is divisible by 6 iff it is even and a 3-cycle rotated
-- n times from (true, false, false) is back at true
divisibleBy6 :
  E Γ (Nat (Bool' A) ⇒ (Nat (Bool' A × (Bool' A × Bool' A)) ⇒ Bool' A))
divisibleBy6 = λ- (λ- (app2 both (app isEven v1)
  (first (app2 v0 rotate ⟨ churchTrue , ⟨ churchFalse , churchFalse ⟩ ⟩))))
  where
  rotate : ∀ {Γ A} → E Γ ((Bool' A × (Bool' A × Bool' A))
                      ⇒ (Bool' A × (Bool' A × Bool' A)))
  rotate = λ- ⟨ second (second v0) , ⟨ first v0 , first (second v0) ⟩ ⟩

-- Church lists: a list is its own right fold
List' : Ty → Ty → Ty
List' X R = (X ⇒ (R ⇒ R)) ⇒ (R ⇒ R)

nil : E Γ (List' X R)
nil = λ- (λ- v0)

cons : E Γ (X ⇒ (List' X R ⇒ List' X R))
cons = λ- (λ- (λ- (λ- (app2 v1 v3 (app2 v2 v1 v0)))))

-- map over a Church list
mapList : E Γ ((X ⇒ A) ⇒ (List' X R ⇒ List' A R))
mapList = λ- (λ- (λ- (λ- (app2 v2 (λ- (λ- (app2 v3 (app v5 v1) v0))) v0))))

-- sum of a list of numerals
sumList : E Γ (List' (Nat A) (Nat A) ⇒ Nat A)
sumList = λ- (app2 v0 plus churchZero)

square : E Γ (Nat A ⇒ Nat A)
square = λ- (app2 times v0 v0)

UpToState : Ty → Ty
UpToState A = Nat A × List' (Nat A) (Nat A)

-- upTo n is the list n, …, 1: iterates (k, l) ↦ (k + 1, (k + 1) ∷ l)
uptoStep : E Γ (UpToState A ⇒ UpToState A)
uptoStep = λ- ⟨ app churchSuc (first v0)
              , app2 cons (app churchSuc (first v0)) (second v0) ⟩

upTo : E Γ (Nat (UpToState A) ⇒ List' (Nat A) (Nat A))
upTo = λ- (second (app2 v0 uptoStep ⟨ churchZero , nil ⟩))

-- sumOfSquares n is 1² + … + n²
sumOfSquares : E Γ (Nat (UpToState A) ⇒ Nat A)
sumOfSquares = λ- (app sumList (app2 mapList square (app upTo v0)))
