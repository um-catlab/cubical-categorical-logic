{-# OPTIONS --lossy-unification #-}
module Gluing.Bench.CartesianClosedCategory.NbE where

-- Normalization by evaluation for the free CCC: open programs over
-- Church numerals normalize by refl to the expected β-short η-long
-- normal form. Contexts are product trees and variables are morphisms
-- of the free cartesian category.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (isEven; isOdd)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Base
  hiding (eval)
open import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
  using (_×_; ↑_; ⊤)
open import Gluing.CartesianClosedCategory.Renamings
open import Gluing.CartesianClosedCategory.NormalForms
open import Gluing.CartesianClosedCategory.NbE.Normalise
open import Gluing.CartesianClosedCategory.BoolNatCanonicity.UncurriedElim
open import Gluing.Bench.Reference
open import Gluing.Bench.CartesianClosedCategory.Church
  renaming (app to app')

Cx = Ctx ×⇒QUIVER
NF = Nf ×⇒QUIVER

-- normalize a term in context Γ
nf : ∀ Γ {A} → E (contextType ×⇒QUIVER Γ) A → NF Γ A
nf Γ = normalise ×⇒QUIVER

α : Ty
α = N

private variable
  Γ : Cx
  A B C : Ty

-- the context under the two λs of a Church numeral: f then x
ChurchContext : Cx → Cx
ChurchContext Γ = (Γ × (↑ (α ⇒ α))) × (↑ α)

vz' : Var ×⇒QUIVER (Γ × (↑ A)) A
vz' = vz ×⇒QUIVER

vs' : Var ×⇒QUIVER Γ A → Var ×⇒QUIVER (Γ × (↑ B)) A
vs' = vs ×⇒QUIVER

-- the normal forms x and f (… (f x)) in the body of a numeral
varX : NF (ChurchContext Γ) α
varX = ne (var vz')

applyVarF : ℕ → NF (ChurchContext Γ) α → NF (ChurchContext Γ) α
applyVarF zero t = t
applyVarF (suc m) t = ne (app (var (vs' vz')) (applyVarF m t))

-- the normal form of the Church numeral n
numeralNf : ℕ → NF Γ (Nat α)
numeralNf m = lam (lam (applyVarF m varX))

-- the η-expanded normal form λ y. f y
etaF : NF (ChurchContext Γ) (α ⇒ α)
etaF = lam (ne (app (var (vs' (vs' vz'))) (ne (var vz'))))

-- iterateVar x t is the neutral x (λ y. f y) t
iterateVar : Var ×⇒QUIVER Γ (Nat α) →
  NF (ChurchContext Γ) α → NF (ChurchContext Γ) α
iterateVar x t = ne (app (app (var (vs' (vs' x))) etaF) t)

-- normal form of v0 + k: λ f x. v0 (λ y. f y) (fᵏ x)
expectedPlus : ℕ → NF (⊤ × (↑ Nat α)) (Nat α)
expectedPlus k = lam (lam (iterateVar vz' (applyVarF k varX)))

-- normal form of k · v0: k nested applications of v0
expectedTimes : ℕ → NF (⊤ × (↑ Nat α)) (Nat α)
expectedTimes k = lam (lam (go k))
  where
  go : ℕ → NF (ChurchContext (⊤ × (↑ Nat α))) α
  go zero = varX
  go (suc m) = iterateVar vz' (go m)

-- normal form of if v0 then 2ᵏ else k²
expectedIf : ℕ → NF (⊤ × (↑ Bool' (Nat α))) (Nat α)
expectedIf k = lam (lam (ne (app (app (app (app (var (vs' (vs' vz')))
  (numeralNf (powℕ 2 k))) (numeralNf (k · k))) etaF) varX)))

-- normal form of the sum of v0 mapped over k, …, 1
expectedMapSum : ℕ → NF (⊤ × (↑ (Nat α ⇒ Nat α))) (Nat α)
expectedMapSum k = lam (lam (go k))
  where
  go : ℕ → NF (ChurchContext (⊤ × (↑ (Nat α ⇒ Nat α)))) α
  go zero = varX
  go (suc m) =
    ne (app (app (app (var (vs' (vs' vz'))) (numeralNf (suc m))) etaF) (go m))

private variable
  Δ : Ty

-- the S, K, I combinators and B = S (K S) K, T = S (K (S I)) K
combI : E Δ (A ⇒ A)
combI = λ- v0

combK : E Δ (A ⇒ (B ⇒ A))
combK = λ- (λ- v1)

combS : E Δ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
combS = λ- (λ- (λ- (app' (app' v2 v0) (app' v1 v0))))

combB : E Δ ((B ⇒ C) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
combB = app2 combS (app' combK combS) combK

combT : E Δ (A ⇒ ((A ⇒ B) ⇒ B))
combT = app2 combS (app' combK (app' combS combI)) combK

skiZero : E Δ (Nat A)
skiZero = app' combK combI

skiSuc : E Δ (Nat A ⇒ Nat A)
skiSuc = app' combS combB

-- numerals and arithmetic built from combinators only
skiNumeral : ℕ → E Δ (Nat A)
skiNumeral zero = skiZero
skiNumeral (suc k) = app' skiSuc (skiNumeral k)

skiTimes : E Δ (Nat A ⇒ (Nat A ⇒ Nat A))
skiTimes = combB

skiPower : E Δ (Nat A ⇒ (Nat (A ⇒ A) ⇒ Nat A))
skiPower = combT

-- the programs normalized on numerals
normalPower normalSkiPower normalSkiTimes : ℕ → ℕ → NF ⊤ (Nat α)
normalPower a b = nf ⊤ (app2 power (churchNumeral a) (churchNumeral b))
normalSkiPower a b = nf ⊤ (app2 skiPower (skiNumeral a) (skiNumeral b))
normalSkiTimes a b = nf ⊤ (app2 skiTimes (skiNumeral a) (skiNumeral b))

normalFibonacci : ℕ → NF ⊤ (Nat α)
normalFibonacci k = nf ⊤ (app' fibonacci (churchNumeral k))

-- v0 + k and k · v0 for a numeral variable v0
normalPlusVar normalTimesVar : ℕ → NF (⊤ × (↑ Nat α)) (Nat α)
normalPlusVar k = nf (⊤ × (↑ Nat α)) (app2 plus v0 (churchNumeral k))
normalTimesVar k = nf (⊤ × (↑ Nat α)) (app2 times (churchNumeral k) v0)

-- if v0 then 2ᵏ else k² for a boolean variable v0
normalIf : ℕ → NF (⊤ × (↑ Bool' (Nat α))) (Nat α)
normalIf k = nf (⊤ × (↑ Bool' (Nat α)))
  (app2 (app' ifThenElse v0) (app2 power 2 (churchNumeral k))
    (app2 times (churchNumeral k) (churchNumeral k)))

-- the sum of a function variable v0 mapped over k, …, 1
normalMapSum : ℕ → NF (⊤ × (↑ (Nat α ⇒ Nat α))) (Nat α)
normalMapSum k = nf (⊤ × (↑ (Nat α ⇒ Nat α)))
  (app' sumList (app2 mapList v0 (app' upTo (churchNumeral k))))

tests : List Test
tests =
  -- closed programs normalize to numerals
    test! (normalPower 2 5 ≡ numeralNf (powℕ 2 5))
  ∷ test! (normalFibonacci 6 ≡ numeralNf (fibℕ 6))
  -- open programs normalize to stuck applications of v0
  ∷ test! (normalPlusVar 64 ≡ expectedPlus 64)
  ∷ test! (normalTimesVar 32 ≡ expectedTimes 32)
  ∷ test! (normalIf 5 ≡ expectedIf 5)
  ∷ test! (normalMapSum 5 ≡ expectedMapSum 5)
  -- combinator programs normalize to numerals
  ∷ test! (normalSkiPower 2 2 ≡ numeralNf (powℕ 2 2))
  ∷ test! (normalSkiTimes 3 3 ≡ numeralNf (3 · 3))
  ∷ []
