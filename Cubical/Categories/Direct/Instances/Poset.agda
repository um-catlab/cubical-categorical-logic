-- A well-ordered poset is a (thin) direct category.
module Cubical.Categories.Direct.Instances.Poset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base

private
  variable
    ℓ ℓ' : Level

module _ (Wo : WFOrder ℓ ℓ') where
  open WFOrder Wo
  open Category

  -- the poset (D, ≤) as a thin category
  PosetCat : Category ℓ (ℓ-max ℓ ℓ')
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
