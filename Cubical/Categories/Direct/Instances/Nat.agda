-- ℕ with the usual `<` as a well-ordered poset = the "topos of trees" base.
module Cubical.Categories.Direct.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; suc ; isSetℕ)
open import Cubical.Data.Nat.Order.Recursive using (_<_ ; isProp≤ ; <-trans)
import Cubical.Data.Nat.Order.Recursive as NatOrd

open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Poset

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
