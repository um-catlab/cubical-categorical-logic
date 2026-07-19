-- ℕ with the usual `<` as a well-ordered poset = the "topos of trees" base.
module Cubical.Categories.Direct.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (isPropΣ)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Nat.Order.Recursive using (_<_ ; isProp≤ ; <-trans ; ≤-refl ; ≤-split)
import Cubical.Data.Nat.Order.Recursive as NatOrd
import Cubical.Data.Nat.Order as Ord
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Sum as Sum using (inl ; inr)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Poset
import Cubical.Categories.Direct.Predecessor as P

ℕWFOrder : WFOrder ℓ-zero ℓ-zero
ℕWFOrder = record
  { D       = ℕ
  ; isSetD  = isSetℕ
  ; _<_     = _<_
  ; isProp< = λ a b → isProp≤ {suc a} {b}
  ; trans<  = λ {a} {b} {c} → <-trans {a} {b} {c}
  ; wf<     = NatOrd.WellFounded.wf-<
  }

ℕCat = PosetCat ℕWFOrder

ℕDirect : DirectStr {C = ℕCat} ℕWFOrder
ℕDirect = PosetDirect ℕWFOrder

-- bridge from the Σ-style order of `Cubical.Data.Nat.Order` to ℕWFOrder's
-- Eq-world ≤ (used by Reedy instances whose degree bounds come from
-- combinatorics phrased with the Σ-style order)
<→Wo< : ∀ {a b} → a Ord.< b → a < b
<→Wo< {a}     {zero}  p = Empty.rec (Ord.¬-<-zero p)
<→Wo< {zero}  {suc b} p = tt
<→Wo< {suc a} {suc b} p = <→Wo< {a} {b} (Ord.pred-≤-pred p)

≤→Wo≤ : ∀ {a b} → a Ord.≤ b → WFOrder._≤_ ℕWFOrder a b
≤→Wo≤ {a} {b} a≤b with a Ord.≟ b
... | Ord.lt a<b = inl (<→Wo< a<b)
... | Ord.eq a≡b = inr (Eq.pathToEq a≡b)
... | Ord.gt b<a = Empty.rec (Ord.¬m<m (Ord.≤<-trans a≤b b<a))

-- every successor `suc m` has `m` as predecessor: the strict downset
-- of `suc m` is represented by `m`
sucPred : ∀ m → P.isPredOf ℕDirect (suc m) m
sucPred m = record
  { ρ    = inl (≤-refl m)
  ; p≺x  = ≤-refl m
  ; univ = λ y →
      propBiimpl→Equiv (WFOrder.isProp≤ ℕWFOrder)
        (isPropΣ (WFOrder.isProp≤ ℕWFOrder)
          (λ _ → isProp≤ {suc y} {suc m}))
        _
        (λ (g , q) → Sum.map (λ z → z) Eq.pathToEq (≤-split {y} {m} q))
        .snd
  }

ℕPredecessors : P.Predecessors ℕDirect
ℕPredecessors zero    = P.minimal (λ y h → h)
ℕPredecessors (suc m) = P.hasPred m (sucPred m)
