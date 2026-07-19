-- Extended naturals `Maybe ℕ` (with `∞ = nothing`) and their min-plus
-- (tropical) semiring — `⊕ = min`, `⊗ = +`.  Used for shortest-path costs.
module Cubical.Data.Nat.More where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; +-comm ; +-zero ; +-assoc ; isSetℕ)
open import Cubical.Data.Maybe using (Maybe ; nothing ; just ; isOfHLevelMaybe)
open import Cubical.Data.Empty as ⊥ using (⊥)

Cost : Type
Cost = Maybe ℕ

pattern ∞ = nothing

isSetCost : isSet Cost
isSetCost = isOfHLevelMaybe 0 isSetℕ

minℕ : ℕ → ℕ → ℕ
minℕ zero    _       = zero
minℕ (suc _) zero    = zero
minℕ (suc x) (suc y) = suc (minℕ x y)

_⊕_ : Cost → Cost → Cost        -- ⊕ = min : take the cheaper route
∞      ⊕ y      = y
just x ⊕ ∞      = just x
just x ⊕ just y = just (minℕ x y)

_⊗_ : Cost → Cost → Cost        -- ⊗ = + : extend a route by one edge
∞      ⊗ _      = ∞
just _ ⊗ ∞      = ∞
just x ⊗ just y = just (x + y)

infixr 6 _⊕_
infixr 7 _⊗_

minℕ-comm : ∀ x y → minℕ x y ≡ minℕ y x
minℕ-comm zero    zero    = refl
minℕ-comm zero    (suc _) = refl
minℕ-comm (suc _) zero    = refl
minℕ-comm (suc x) (suc y) = cong suc (minℕ-comm x y)

minℕ-idem : ∀ x → minℕ x x ≡ x
minℕ-idem zero    = refl
minℕ-idem (suc x) = cong suc (minℕ-idem x)

minℕ-assoc : ∀ x y z → minℕ (minℕ x y) z ≡ minℕ x (minℕ y z)
minℕ-assoc zero    _       _       = refl
minℕ-assoc (suc _) zero    _       = refl
minℕ-assoc (suc _) (suc _) zero    = refl
minℕ-assoc (suc x) (suc y) (suc z) = cong suc (minℕ-assoc x y z)

+-minℕ-distribˡ : ∀ z x y → z + minℕ x y ≡ minℕ (z + x) (z + y)
+-minℕ-distribˡ zero    x y = refl
+-minℕ-distribˡ (suc z) x y = cong suc (+-minℕ-distribˡ z x y)

minℕ-+-distrib : ∀ x y z → minℕ x y + z ≡ minℕ (x + z) (y + z)
minℕ-+-distrib x y z =
    +-comm (minℕ x y) z ∙ +-minℕ-distribˡ z x y
  ∙ cong₂ minℕ (+-comm z x) (+-comm z y)

⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
⊕-comm ∞        ∞        = refl
⊕-comm ∞        (just _) = refl
⊕-comm (just _) ∞        = refl
⊕-comm (just x) (just y) = cong just (minℕ-comm x y)

⊕-idem : ∀ x → x ⊕ x ≡ x
⊕-idem ∞        = refl
⊕-idem (just x) = cong just (minℕ-idem x)

⊕-assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
⊕-assoc ∞        _        _        = refl
⊕-assoc (just _) ∞        _        = refl
⊕-assoc (just _) (just _) ∞        = refl
⊕-assoc (just x) (just y) (just z) = cong just (minℕ-assoc x y z)

⊗-distribˡ : ∀ x y z → (x ⊕ y) ⊗ z ≡ (x ⊗ z) ⊕ (y ⊗ z)
⊗-distribˡ ∞        _        _        = refl
⊗-distribˡ (just _) ∞        ∞        = refl
⊗-distribˡ (just _) ∞        (just _) = refl
⊗-distribˡ (just _) (just _) ∞        = refl
⊗-distribˡ (just x) (just y) (just z) = cong just (minℕ-+-distrib x y z)

-- the min-plus order:  x ⊑ y  means "x is no more expensive than y".
_⊑_ : Cost → Cost → Type
x ⊑ y = x ⊕ y ≡ x

⊑-refl : ∀ {x} → x ⊑ x
⊑-refl {x} = ⊕-idem x

⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans {x} {y} {z} p q =
  cong (_⊕ z) (sym p) ∙ ⊕-assoc x y z ∙ cong (x ⊕_) q ∙ p

⊕-lb₁ : ∀ x y → (x ⊕ y) ⊑ x
⊕-lb₁ x y = ⊕-assoc x y x ∙ cong (x ⊕_) (⊕-comm y x)
          ∙ sym (⊕-assoc x x y) ∙ cong (_⊕ y) (⊕-idem x)

⊕-lb₂ : ∀ x y → (x ⊕ y) ⊑ y
⊕-lb₂ x y = ⊕-assoc x y y ∙ cong (x ⊕_) (⊕-idem y)

-- skip the head of a ⊕-chain, keeping a lower bound on the tail
⊕-skip : ∀ x {y z} → y ⊑ z → (x ⊕ y) ⊑ z
⊕-skip x p = ⊑-trans (⊕-lb₂ x _) p

⊗-monoˡ : ∀ {x x'} y → x ⊑ x' → (x ⊗ y) ⊑ (x' ⊗ y)
⊗-monoˡ {x} {x'} y p = sym (⊗-distribˡ x x' y) ∙ cong (_⊗ y) p

⊑∞ : ∀ x → x ⊑ ∞
⊑∞ ∞        = refl
⊑∞ (just _) = refl

⊑-antisym : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
⊑-antisym {x} {y} p q = sym p ∙ ⊕-comm x y ∙ q

∞≢just : ∀ {c : ℕ} → ∞ ≡ just c → ⊥
∞≢just p = subst (λ { ∞ → Unit ; (just _) → ⊥ }) p tt

-- a `⊕` (min) is always realised by one of its arguments — the key fact
-- behind attainment.
minℕ-select : ∀ x y → (minℕ x y ≡ x) ⊎ (minℕ x y ≡ y)
minℕ-select zero    y       = inl refl
minℕ-select (suc x) zero    = inr refl
minℕ-select (suc x) (suc y) with minℕ-select x y
... | inl p = inl (cong suc p)
... | inr q = inr (cong suc q)

⊕-select : ∀ x y → (x ⊕ y ≡ x) ⊎ (x ⊕ y ≡ y)
⊕-select ∞        y        = inr refl
⊕-select (just x) ∞        = inl refl
⊕-select (just x) (just y) with minℕ-select x y
... | inl p = inl (cong just p)
... | inr q = inr (cong just q)

-- ⊗ is a monoid with unit `just 0` (this is (ℕ,+,0) with ∞ absorbing) —
-- the structure delooped into the cost category `BCost`.
⊗-unitˡ : ∀ c → just 0 ⊗ c ≡ c
⊗-unitˡ ∞        = refl
⊗-unitˡ (just y) = refl

⊗-unitʳ : ∀ c → c ⊗ just 0 ≡ c
⊗-unitʳ ∞        = refl
⊗-unitʳ (just x) = cong just (+-zero x)

⊗-assoc : ∀ x y z → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
⊗-assoc ∞        y        z        = refl
⊗-assoc (just x) ∞        z        = refl
⊗-assoc (just x) (just y) ∞        = refl
⊗-assoc (just x) (just y) (just z) = cong just (sym (+-assoc x y z))
