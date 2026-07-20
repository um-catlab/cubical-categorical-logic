-- The walking cospan `L → M ← R` as a thin direct category
module Cubical.Categories.Direct.Instances.Cospan where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥ using (⊥ ; isProp⊥)
open import Cubical.Data.Sum using (inl ; inr)
import Cubical.Data.Equality as Eq
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Thin using (ThinCategory)
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)

data Ob : Type where
  L R M : Ob

Hom : Ob → Ob → Type
Hom L L = Unit
Hom L R = ⊥
Hom L M = Unit
Hom R L = ⊥
Hom R R = Unit
Hom R M = Unit
Hom M L = ⊥
Hom M R = ⊥
Hom M M = Unit

reflH : ∀ {x} → Hom x x
reflH {L} = tt
reflH {R} = tt
reflH {M} = tt

transH : ∀ {x y z} → Hom x y → Hom y z → Hom x z
transH {L} {L}     f g = g
transH {L} {R}     f g = ⊥.rec f
transH {L} {M} {L} f g = ⊥.rec g
transH {L} {M} {R} f g = ⊥.rec g
transH {L} {M} {M} f g = tt
transH {R} {L}     f g = ⊥.rec f
transH {R} {R}     f g = g
transH {R} {M} {L} f g = ⊥.rec g
transH {R} {M} {R} f g = ⊥.rec g
transH {R} {M} {M} f g = tt
transH {M} {L}     f g = ⊥.rec f
transH {M} {R}     f g = ⊥.rec f
transH {M} {M}     f g = g

isPropHomₖ : ∀ {x y} → isProp (Hom x y)
isPropHomₖ {L} {L} = isPropUnit
isPropHomₖ {L} {R} = isProp⊥
isPropHomₖ {L} {M} = isPropUnit
isPropHomₖ {R} {L} = isProp⊥
isPropHomₖ {R} {R} = isPropUnit
isPropHomₖ {R} {M} = isPropUnit
isPropHomₖ {M} {L} = isProp⊥
isPropHomₖ {M} {R} = isProp⊥
isPropHomₖ {M} {M} = isPropUnit

CospanCat : Category ℓ-zero ℓ-zero
CospanCat = ThinCategory Ob Hom reflH transH isPropHomₖ

deg : Ob → ℕ
deg L = 0
deg R = 0
deg M = 1

CospanDirect : DirectStr {C = CospanCat} ℕWFOrder
CospanDirect = mkDirectStr {C = CospanCat} ℕWFOrder deg non-dec
  where
    non-dec : {x y : Ob} → Hom x y → WFOrder._≤_ ℕWFOrder (deg x) (deg y)
    non-dec {L} {L} _ = inr Eq.refl
    non-dec {L} {R} f = ⊥.rec f
    non-dec {L} {M} _ = inl tt
    non-dec {R} {L} f = ⊥.rec f
    non-dec {R} {R} _ = inr Eq.refl
    non-dec {R} {M} _ = inl tt
    non-dec {M} {L} f = ⊥.rec f
    non-dec {M} {R} f = ⊥.rec f
    non-dec {M} {M} _ = inr Eq.refl
