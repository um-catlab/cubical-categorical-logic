{-# OPTIONS --lossy-unification #-}
module Gluing.Bench.BiCartesianClosedCategory.Church where

-- Canonicity for the free BiCCC on Church numerals: polynomial
-- evaluation and parity at the bit type.

open import Cubical.Foundations.Prelude
open import Agda.Builtin.FromNat
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Nat using (ℕ; zero; suc; _·_)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Unit using (Unit)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Gluing.BiCartesianClosedCategory.BoolNatCanonicity.Forded
  using (nat; [ze]; [su])
open import Gluing.Bench.Reference
open import Gluing.Bench.BiCartesianClosedCategory.Base
open import Gluing.Bench.BiCartesianClosedCategory.Circuits using (notG)

ChurchNat : Ob → Ob
ChurchNat A = (A ⇒ A) ⇒ (A ⇒ A)

private variable
  Γ A : Ob

-- the Church numeral of k; numeral literals elaborate to this
church : ℕ → E Γ (ChurchNat A)
church k = lam' (lam' (iter k))
  where
  iter : ℕ → E ((_ × (_ ⇒ _)) × _) _
  iter zero = v0
  iter (suc k) = app v1 (iter k)

instance
  numeral : Number (E Γ (ChurchNat A))
  numeral .Number.Constraint _ = Unit
  numeral .Number.fromNat k = church k

-- addition and multiplication of Church numerals
plus times : E Γ (ChurchNat A ⇒ (ChurchNat A ⇒ ChurchNat A))
plus = lam' (lam' (lam' (lam' (app2 v3 v1 (app2 v2 v1 v0)))))
times = lam' (lam' (lam' (app v2 (app v1 v0))))

-- Horner evaluation of the polynomial with coefficients as at x
horner : List ℕ → E Γ (ChurchNat A) → E Γ (ChurchNat A)
horner [] x = 0
horner (a ∷ as) x = app2 plus (church a) (app2 times x (horner as x))

-- decode a numeral at the base type nat via suc and zero
decodeNat : E ⊤ (ChurchNat (↑ nat)) → E ⊤ (↑ nat)
decodeNat c = app2 c (lam' (π₂' ⋆ₑ [su])) [ze]

-- parity of a numeral by iterating not on a bit
churchIsEven : E ⊤ (ChurchNat Bit) → E ⊤ Bit
churchIsEven c = app2 c (lam' (π₂' ⋆ₑ notG)) tru

-- reference Horner evaluation on ℕ
refHorner : List ℕ → ℕ → ℕ
refHorner [] x = 0
refHorner (a ∷ as) x = a Nat.+ x · refHorner as x

-- the programs run by canonicity on concrete inputs
hornerAt : List ℕ → ℕ → ℕ
hornerAt as x = canonicalNat (decodeNat (horner as (church x)))

isEvenNumeral : ℕ → Bool
isEvenNumeral k = canonicalBit (churchIsEven (church k))

tests : List Test
tests =
  -- 1 + 2x + 3x² at x = 2
    test! (hornerAt (1 ∷ 2 ∷ 3 ∷ []) 2 ≡ refHorner (1 ∷ 2 ∷ 3 ∷ []) 2)
  -- 50 is even
  ∷ test! (isEvenNumeral 50 ≡ evenℕ 50)
  ∷ []
