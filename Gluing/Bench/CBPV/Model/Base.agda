{-# OPTIONS --prop --lossy-unification #-}
module Gluing.Bench.CBPV.Model.Base where

-- Shared syntax for CBPV programs over algebraic theories (reader,
-- writer, state), run in the concrete models by canonicity.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Data.FinData using (Fin; zero; suc; toℕ)
open import Cubical.Data.List using (List; _∷_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Mod using (_mod_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Categories.Instances.WalkingArrow
  renaming (Vertex to Kind; l to 𝒱; r to 𝒞)
open import Cubical.Algebra.Theory.Base
open import Gluing.Bench.Reference using (half; odd)
open import
  Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.ModelEnriched.Additive
  using (module CBPV)
import Gluing.CBPV.Model.Additive as Generic

private
  variable
    ℓO ℓA ℓE ℓEA : Level

-- n-digit words, least significant digit first
Word : Type → ℕ → Type
Word D zero = Unit
Word D (suc n) = D × Word D n

isSetWord : ∀ {D} → isSet D → ∀ n → isSet (Word D n)
isSetWord isSetD zero = isSetUnit
isSetWord isSetD (suc n) = isSet× isSetD (isSetWord isSetD n)

rep : ∀ {D} n → D → Word D n
rep zero d = tt
rep (suc n) d = d , rep n d

mapWord : ∀ {D D'} n → (D → D') → Word D n → Word D' n
mapWord zero f w = tt
mapWord (suc n) f (d , w) = f d , mapWord n f w

unlift : ∀ {ℓ ℓ'} {X : Type ℓ} → X × Lift ℓ' Bool → X × Bool
unlift (x , lift b) = x , b

mapFst : ∀ {X X' Y : Type} → (X → X') → X × Y → X' × Y
mapFst f (x , y) = f x , y

consFst : ∀ {X Y : Type} → X → List X × Y → List X × Y
consFst x (xs , y) = x ∷ xs , y

-- majority, the carry of a full adder
maj : Bool → Bool → Bool → Bool
maj a b c = (a and b) or (c and (a or b))

bitℕ : Bool → ℕ
bitℕ b = if b then 1 else 0

-- the low n bits of k
bits : ∀ n → ℕ → Word Bool n
bits zero k = tt
bits (suc n) k = odd k , bits n (half k)

-- the value of a word read most significant digit first
valMSB : ∀ n → ℕ → Word Bool n → ℕ
valMSB zero acc w = acc
valMSB (suc n) acc (b , w) = valMSB n (2 · acc + bitℕ b) w

-- a fixed pseudo-random word
patWord : ∀ n → ℕ → Word Bool n
patWord zero k = tt
patWord (suc n) k = odd (half (k · 7 + 3)) , patWord n (suc k)

finMod : ∀ k → ℕ → Fin (suc k)
finMod k n = embed k (n mod suc k)
  where
  embed : ∀ k → ℕ → Fin (suc k)
  embed zero m = zero
  embed (suc k) zero = zero
  embed (suc k) (suc m) = suc (embed k m)

-- one step of the remainder automaton: q ↦ (2q + b) mod (k + 1)
dbl : ∀ k → Fin (suc k) → Bool → Fin (suc k)
dbl k q b = finMod k (2 · toℕ q + bitℕ b)

module Syntax (T : Theory ℓO ℓA ℓE ℓEA) where
  open Generic.BoolModelSyntax T public
  open CBPV T BaseTy public

  infixl 5 _>>=_
  _>>=_ : ∀ {A A' : Ob 𝒱} {B : Ob 𝒞}
    → Tm _ A ([F] A') → Tm _ A' B → Tm _ A B
  M >>= N = seqS M ([bind] N)

  return : ∀ {A A' : Ob 𝒱} → Tm _ A A' → Tm _ A ([F] A')
  return V = seqS V [ret]

  -- D X tags a value with one bit
  D : Ob 𝒱 → Ob 𝒱
  D X = X [+] X

  tagB : ∀ {X : Ob 𝒱} → Bool → Tm _ X (D X)
  tagB true = [+I1]
  tagB false = [+I2]

  caseB : ∀ {k} {X : Ob 𝒱} {B : Ob k} → (Bool → Tm _ X B) → Tm _ (D X) B
  caseB f = [+E] (f true) (f false)

  tagQ : ∀ {X : Ob 𝒱} → Bool × Bool → Tm _ X (D (D X))
  tagQ (a , b) = seqS (tagB b) (tagB a)

  caseQ : ∀ {k} {X : Ob 𝒱} {B : Ob k}
    → (Bool × Bool → Tm _ X B) → Tm _ (D (D X)) B
  caseQ f = caseB λ a → caseB λ b → f (a , b)

  -- Tag k X tags a value with one of k tags
  Tag : ℕ → Ob 𝒱 → Ob 𝒱
  Tag zero X = [0]
  Tag (suc k) X = X [+] Tag k X

  tagFin : ∀ {k} {X : Ob 𝒱} → Fin k → Tm _ X (Tag k X)
  tagFin zero = [+I1]
  tagFin (suc q) = seqS (tagFin q) [+I2]

  caseFin : ∀ {k k'} {X : Ob 𝒱} {B : Ob k'}
    → (Fin k → Tm _ X B) → Tm _ (Tag k X) B
  caseFin {k = zero} f = [0E]
  caseFin {k = suc k} f = [+E] (f zero) (caseFin λ q → f (suc q))

  module Digits {Digit : Type} (L : Ob 𝒱 → Ob 𝒱)
    (tag : ∀ {X : Ob 𝒱} → Digit → Tm _ X (L X))
    (case : ∀ {k} {X : Ob 𝒱} {B : Ob k}
      → (Digit → Tm _ X B) → Tm _ (L X) B)
    where
    Num : ℕ → Ob 𝒱 → Ob 𝒱
    Num zero A = A
    Num (suc n) A = L (Num n A)

    quoteNum : ∀ n {A : Ob 𝒱} → Word Digit n → Tm _ A (Num n A)
    quoteNum zero _ = idS
    quoteNum (suc n) (d , w) = seqS (quoteNum n w) (tag d)

    caseNum : ∀ n {k} {A : Ob 𝒱} {B : Ob k}
      → (Word Digit n → Tm _ A B) → Tm _ (Num n A) B
    caseNum zero f = f tt
    caseNum (suc n) f = case λ d → caseNum n λ w → f (d , w)

    -- ripple a carry through the digits, applying fs digitwise
    ripple : ∀ n {A : Ob 𝒱} → Word (Digit → Bool → Digit × Bool) n → Bool
      → Tm _ (Num n A) ([F] (D (Num n A)))
    ripple zero fs c = return (tagB c)
    ripple (suc n) (f , fs) c = case λ d →
      ripple n fs (f d c .snd) >>= caseB λ c' →
        return (seqS (tag (f d c .fst)) (tagB c'))

  module Bits = Digits D tagB caseB
  module Pairs = Digits (λ X → D (D X)) tagQ caseQ

  module DFA (k : ℕ)
    (log : ∀ {A : Ob 𝒱} {B : Ob 𝒞} → Fin (suc k) → Tm _ A B → Tm _ A B)
    where
    open Bits

    -- feed the bits to the remainder automaton, logging each state
    scan : ∀ n {A : Ob 𝒱}
      → Tm _ (Tag (suc k) (Num n A)) ([F] (Tag (suc k) A))
    scan zero = [ret]
    scan (suc n) = caseFin (λ q → caseB λ b →
      log (dbl k q b) (return (tagFin (dbl k q b)))) >>= scan n

    accept : Tm _ (Tag (suc k) UnitTy) FBoolTy
    accept = caseFin λ where
      zero → return tru
      (suc q) → return fls

    -- whether bs is divisible by k + 1
    runAutomaton : ∀ n → Word Bool n → Tm _ UnitTy FBoolTy
    runAutomaton n bs =
      seqS (seqS (quoteNum n bs) (tagFin zero)) (scan n) >>= accept
