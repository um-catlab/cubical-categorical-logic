-- A well-ordered poset is a (thin) direct category.
module Cubical.Categories.Direct.Instances.Poset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sum

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf.StrictHom.Base using (PshHomStrict)
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.StrictDownset

open PshHomStrict

private
  variable
    ℓ : Level

module _ (Wo : WFOrder ℓ ℓ) where
  open WFOrder Wo
  open Category

  -- the poset `(D, ≤)` as a thin category
  PosetCat : Category ℓ ℓ
  PosetCat .ob              = D
  PosetCat .Hom[_,_]        = _≤_
  PosetCat .id              = ≤-refl
  PosetCat ._⋆_             = ≤-trans
  PosetCat .⋆IdL _          = isProp≤ _ _
  PosetCat .⋆IdR _          = isProp≤ _ _
  PosetCat .⋆Assoc _ _ _    = isProp≤ _ _
  PosetCat .isSetHom        = isProp→isSet isProp≤

  PosetDirect : DirectStr {C = PosetCat} Wo
  PosetDirect = mkDirectStr {C = PosetCat} Wo (λ x → x) (λ f → f)

  löbWF : ∀ {ℓF} (A : D → hSet (ℓ-max ℓF ℓ))
        → (∀ x → (∀ y → y < x → ⟨ A y ⟩) → ⟨ A x ⟩)
        → ∀ x → ⟨ A x ⟩
  löbWF {ℓF} A step = löbFam PosetDirect {ℓF = ℓF} A
    (λ x α → step x (λ y y<x → α .N-ob y (inl y<x , y<x) y (inr refl)))
