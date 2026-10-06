module Cubical.Categories.Direct.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Nat.Order.Recursive using (_<_ ; isProp≤ ; <-trans)
import Cubical.Data.Nat.Order.Recursive as NatOrd
import Cubical.Data.Nat.Order as Ord
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty

open import Cubical.Categories.Direct.Base

ℕWFOrder : WFOrder ℓ-zero ℓ-zero
ℕWFOrder = record
  { D = ℕ ; isSetD = isSetℕ ; _<_ = _<_
  ; isProp< = λ a b → isProp≤ {suc a} {b}
  ; trans< = λ {a} {b} {c} → <-trans {a} {b} {c}
  ; wf< = NatOrd.WellFounded.wf-< }

<→Wo< : ∀ {a b} → a Ord.< b → a < b
<→Wo< {a}     {zero}  p = Empty.rec (Ord.¬-<-zero p)
<→Wo< {zero}  {suc b} p = tt
<→Wo< {suc a} {suc b} p = <→Wo< {a} {b} (Ord.pred-≤-pred p)
