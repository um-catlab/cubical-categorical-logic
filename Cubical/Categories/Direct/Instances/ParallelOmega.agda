-- The "parallel ω": like ω = (ℕ, ≤) but with TWO arrows at every step.
--
-- It is the free category on the graph with nodes ℕ and two edges `m → m+1`
-- at each level (`false` and `true`).  Morphisms `m → n` are paths = binary
-- strings of length `n - m`, so for `m < n` there are many of them — genuinely
-- non-thin.  Degree = the number itself; every edge raises it by one, so it is
-- direct.  (Presheaves on it are "ℕ-graded bi-streams": a set at each stage
-- with two restriction maps down a level.)
module Cubical.Categories.Direct.Instances.ParallelOmega where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ)
open import Cubical.Data.Nat.Order.Recursive using (_<_ ; ≤-refl)

open import Cubical.Data.Graph.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.UnderlyingGraph
open import Cubical.Categories.Instances.Free.Category.Base

open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.StrictDownset using (löbStr)
open import Cubical.Categories.Direct.Instances.Poset using (PosetCat)
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)

open Functor

-- the generating graph: two parallel edges m → m+1
ParΩGraph : Graph ℓ-zero ℓ-zero
ParΩGraph .Node = ℕ
ParΩGraph .Edge m n = (n ≡ suc m) × Bool

open FreeCategory ParΩGraph

ParΩ : Category ℓ-zero ℓ-zero
ParΩ = FreeCat

-- the degree functor ParΩ → (ℕ, ≤): identity on nodes, each edge m → m+1 is a
-- strict step.  Its action on morphisms is exactly the non-decreasing witness.
degInterp : GraphHom ParΩGraph (Cat→Graph (PosetCat ℕWFOrder))
degInterp ._$g_ m = m
degInterp ._<$g>_ {m} (n≡sucm , _) = inl (subst (m <_) (sym n≡sucm) (≤-refl m))

degFunctor : Functor ParΩ (PosetCat ℕWFOrder)
degFunctor = Semantics.sem (PosetCat ℕWFOrder) degInterp

ParΩDirect : DirectStr {C = ParΩ} ℕWFOrder
ParΩDirect = mkDirectStr {C = ParΩ} ℕWFOrder (λ m → m) (degFunctor .F-hom)

----------------------------------------------------------------------------
-- Löb on the parallel ω.
--
-- At stage `suc k` the value is built from the value at `k` taken along EACH
-- of the two generating arrows `k → suc k`, and we may combine them with
-- different numbers — different per arrow (`false`/`true`) and per level `k`.
-- Here:  along `false` we add `k`, along `true` we add `suc k`.
----------------------------------------------------------------------------
private
  A : ℕ → hSet ℓ-zero
  A _ = ℕ , isSetℕ

  e₀ e₁ : (k : ℕ) → ParΩ [ k , suc k ]            -- the two generating arrows
  e₀ k = ↑ (refl , false)                          -- source-side
  e₁ k = ↑ (refl , true)                           -- target-side

val : ∀ n → ⟨ A n ⟩
val = löbStr ParΩDirect {ℓF = ℓ-zero} A λ where
  zero    _   → 1
  (suc k) rec → (rec k (e₀ k) (≤-refl k) + k) + (rec k (e₁ k) (≤-refl k) + suc k)

-- it computes:  val (suc k) = 2·val k + 2k+1   ⇒   1, 3, 9, 23, …
_ : val 0 ≡ 1
_ = refl

_ : val 3 ≡ 23
_ = refl
