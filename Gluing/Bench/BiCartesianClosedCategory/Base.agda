{-# OPTIONS --lossy-unification #-}
module Gluing.Bench.BiCartesianClosedCategory.Base where

-- Shared notation for the BiCCC canonicity benchmarks: programs are
-- terms of the forded free BiCCC over the Bool/Nat quiver.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc; _·_)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit)
open import Agda.Builtin.FromNat
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Forded
  using (Expr; _⋆ₑ_; idₑ'; π₁'; π₂'; σ₁'; σ₂'; ⟨_,_⟩'; [_,_]'; !ₑ'; eval'; lam')
  public
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Gluing.BiCartesianClosedCategory.BoolNatCanonicity.Forded
open import Gluing.Bench.Reference using (half; odd)

open Section

Ob = +×⇒Quiver.obExpr +×⇒QUIVER
E = Expr +×⇒QUIVER

private variable
  Γ A B C D F W : Ob

-- apply a morphism to one or two generalized elements
apply : E A B → E Γ A → E Γ B
apply f a = a ⋆ₑ f

apply2 : E (A × B) C → E Γ A → E Γ B → E Γ C
apply2 f a b = ⟨ a , b ⟩' ⋆ₑ f

-- application of a function-typed term
app : E Γ (A ⇒ B) → E Γ A → E Γ B
app f a = ⟨ f , a ⟩' ⋆ₑ eval'

app2 : E Γ (A ⇒ (B ⇒ C)) → E Γ A → E Γ B → E Γ C
app2 f a b = app (app f a) b

-- let a in body, encoded as (λ body) a
letE : E Γ A → E (Γ × A) B → E Γ B
letE a body = app (lam' body) a

-- case analysis on a sum, binding the payload
caseOn : E Γ (A + B) → E (Γ × A) C → E (Γ × B) C → E Γ C
caseOn s l r =
  app (s ⋆ₑ [ lam' (⟨ π₂' , π₁' ⟩' ⋆ₑ l) , lam' (⟨ π₂' , π₁' ⟩' ⋆ₑ r) ]') idₑ'

-- de Bruijn variables: v0 is the innermost binding
v0 : E (Γ × A) A
v0 = π₂'
v1 : E ((Γ × A) × B) A
v1 = π₁' ⋆ₑ v0
v2 : E (((Γ × A) × B) × C) A
v2 = π₁' ⋆ₑ v1
v3 : E ((((Γ × A) × B) × C) × D) A
v3 = π₁' ⋆ₑ v2
v4 : E (((((Γ × A) × B) × C) × D) × F) A
v4 = π₁' ⋆ₑ v3

-- a bit is ⊤ + ⊤, with true the left injection
Bit : Ob
Bit = ⊤ + ⊤

tru fls : E Γ Bit
tru = !ₑ' ⋆ₑ σ₁'
fls = !ₑ' ⋆ₑ σ₂'

quoteBit : Bool → E Γ Bit
quoteBit true = tru
quoteBit false = fls

infix 2 if_then_else_
if_then_else_ : E Γ Bit → E Γ C → E Γ C → E Γ C
if b then t else f = caseOn b (π₁' ⋆ₑ t) (π₁' ⋆ₑ f)

-- n-bit words, least significant bit first
Word : ℕ → Ob
Word zero = ⊤
Word (suc n) = Bit × Word n

-- the word of the low n bits of k
quoteWord : ∀ n → ℕ → E Γ (Word n)
quoteWord zero k = !ₑ'
quoteWord (suc n) k = ⟨ quoteBit (odd k) , quoteWord n (half k) ⟩'

instance
  -- numeral literals denote words
  wordNil : Number (E Γ ⊤)
  wordNil .Number.Constraint _ = Unit
  wordNil .Number.fromNat _ = !ₑ'

  wordCons : ⦃ Number (E Γ W) ⦄ → Number (E Γ (Bit × W))
  wordCons ⦃ w ⦄ .Number.Constraint k = Number.Constraint w (half k)
  wordCons ⦃ w ⦄ .Number.fromNat k ⦃ c ⦄ =
    ⟨ quoteBit (odd k) , Number.fromNat w (half k) ⦃ c ⦄ ⟩'

isInl : ∀ {ℓa ℓb} {X : Type ℓa} {Y : Type ℓb} → X ⊎ Y → Bool
isInl (inl _) = true
isInl (inr _) = false

-- run closed programs by canonicity and read off the result
canonicalBit : E ⊤ Bit → Bool
canonicalBit t = isInl (can t .fst .snd)

canonicalNat : E ⊤ (↑ nat) → ℕ
canonicalNat t = can t .fst .snd .fst

bitℕ : Bool → ℕ
bitℕ true = 1
bitℕ false = 0

-- the value of a canonical word
decodeWord : ∀ n {x} → S .F-obᴰ (Word n) x .fst → ℕ
decodeWord zero r = 0
decodeWord (suc n) r =
  bitℕ (isInl (r .fst .fst .snd .fst .snd))
    Nat.+ 2 · decodeWord n (r .snd .fst .snd .fst .snd)

canonicalWord : ∀ n → E ⊤ (Word n) → ℕ
canonicalWord n t = decodeWord n (can t .fst .snd)
