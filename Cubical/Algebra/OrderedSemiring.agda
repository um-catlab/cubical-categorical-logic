module Cubical.Algebra.OrderedSemiring where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

record OrderedSemiring (ℓ : Level) : Type (ℓ-suc ℓ) where
  infixr 6 _⊕_
  infixr 7 _⊗_
  field
    R          : Type ℓ
    isSetR     : isSet R
    𝟘 𝟙        : R
    _⊕_ _⊗_    : R → R → R
    ⊕-assoc    : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
    ⊕-comm     : ∀ x y → x ⊕ y ≡ y ⊕ x
    ⊕-idem     : ∀ x → x ⊕ x ≡ x
    ⊕-unit     : ∀ x → 𝟘 ⊕ x ≡ x
    ⊗-assoc    : ∀ x y z → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    ⊗-unitˡ    : ∀ x → 𝟙 ⊗ x ≡ x
    ⊗-unitʳ    : ∀ x → x ⊗ 𝟙 ≡ x
    ⊗-annihilˡ : ∀ x → 𝟘 ⊗ x ≡ 𝟘
    ⊗-distribˡ : ∀ x y z → (x ⊕ y) ⊗ z ≡ (x ⊗ z) ⊕ (y ⊗ z)

  -- the induced order:  x ⊑ y  ("x is below y") iff  x ⊕ y ≡ x.
  _⊑_ : R → R → Type ℓ
  x ⊑ y = x ⊕ y ≡ x

  isProp⊑ : ∀ {x y} → isProp (x ⊑ y)
  isProp⊑ = isSetR _ _

  ⊑-refl : ∀ {x} → x ⊑ x
  ⊑-refl {x} = ⊕-idem x

  ⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
  ⊑-trans {x} {y} {z} p q =
    cong (_⊕ z) (sym p) ∙ ⊕-assoc x y z ∙ cong (x ⊕_) q ∙ p

  ⊑-antisym : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
  ⊑-antisym {x} {y} p q = sym p ∙ ⊕-comm x y ∙ q

  -- ⊕ is the meet: it is a lower bound of both arguments …
  ⊕-lb₁ : ∀ x y → (x ⊕ y) ⊑ x
  ⊕-lb₁ x y = ⊕-assoc x y x ∙ cong (x ⊕_) (⊕-comm y x)
            ∙ sym (⊕-assoc x x y) ∙ cong (_⊕ y) (⊕-idem x)

  ⊕-lb₂ : ∀ x y → (x ⊕ y) ⊑ y
  ⊕-lb₂ x y = ⊕-assoc x y y ∙ cong (x ⊕_) (⊕-idem y)

  ⊕-skip : ∀ x {y z} → y ⊑ z → (x ⊕ y) ⊑ z
  ⊕-skip x p = ⊑-trans (⊕-lb₂ x _) p

  -- 𝟘 is the top element.
  ⊑𝟘 : ∀ x → x ⊑ 𝟘
  ⊑𝟘 x = ⊕-comm x 𝟘 ∙ ⊕-unit x

  -- ⊗ is monotone in its left argument (from left-distributivity).
  ⊗-monoˡ : ∀ {x x'} y → x ⊑ x' → (x ⊗ y) ⊑ (x' ⊗ y)
  ⊗-monoˡ {x} {x'} y p = sym (⊗-distribˡ x x' y) ∙ cong (_⊗ y) p
