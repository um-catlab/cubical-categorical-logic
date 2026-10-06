{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Monoidal.Closed where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Dual
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Reindex

private
  variable
    ℓ ℓ' : Level

module _ (M : MonoidalCategory ℓ ℓ') where
  open MonoidalCategory M

  _⊗- : ob → Functor C C
  c ⊗- = ─⊗─ ∘F rinj C C c

  -⊗_ : ob → Functor C C
  -⊗ c = ─⊗─ ∘F linj C C c

  LeftHom : (c d : ob) → Type _
  LeftHom c d = UniversalElement C (reindPsh (c ⊗-) (C [-, d ]))

  RightHom : (c d : ob) → Type _
  RightHom c d = UniversalElement C (reindPsh (-⊗ c) (C [-, d ]))

  LeftClosed : Type _
  LeftClosed = ∀ c d → LeftHom c d

  RightClosed : Type _
  RightClosed = ∀ c d → RightHom c d

module _ (M : MonoidalCategory ℓ ℓ') where
  open UniversalElement

  RightClosed→LeftClosed^co : RightClosed M → LeftClosed (M ^co)
  RightClosed→LeftClosed^co cl c d .vertex = cl c d .vertex
  RightClosed→LeftClosed^co cl c d .element = cl c d .element
  RightClosed→LeftClosed^co cl c d .universal = cl c d .universal

module LeftClosedNotation {M : MonoidalCategory ℓ ℓ'} (cl : LeftClosed M) where
  private
    module M = MonoidalCategory M
  module _ {c d : M.ob} where
    open UniversalElementNotation (cl c d)

    ev : M.Hom[ c M.⊗ vertex , d ]
    ev = element

    lda : ∀ {z} → M.Hom[ c M.⊗ z , d ] → M.Hom[ z , vertex ]
    lda = intro

    ev-β : ∀ {z} (f : M.Hom[ c M.⊗ z , d ]) → (M.id M.⊗ₕ lda f) M.⋆ ev ≡ f
    ev-β f = β

    ⟜-ext : ∀ {z} {f g : M.Hom[ z , vertex ]}
      → (M.id M.⊗ₕ f) M.⋆ ev ≡ (M.id M.⊗ₕ g) M.⋆ ev → f ≡ g
    ⟜-ext = extensionality

  _⟜_ : M.ob → M.ob → M.ob
  d ⟜ c = UniversalElement.vertex (cl c d)

module RightClosedNotation {M : MonoidalCategory ℓ ℓ'} (cl : RightClosed M) where
  private
    module M = MonoidalCategory M
  module _ {c d : M.ob} where
    open UniversalElementNotation (cl c d)

    ev : M.Hom[ vertex M.⊗ c , d ]
    ev = element

    lda : ∀ {z} → M.Hom[ z M.⊗ c , d ] → M.Hom[ z , vertex ]
    lda = intro

    ev-β : ∀ {z} (f : M.Hom[ z M.⊗ c , d ]) → (lda f M.⊗ₕ M.id) M.⋆ ev ≡ f
    ev-β f = β

    ⊸-ext : ∀ {z} {f g : M.Hom[ z , vertex ]}
      → (f M.⊗ₕ M.id) M.⋆ ev ≡ (g M.⊗ₕ M.id) M.⋆ ev → f ≡ g
    ⊸-ext = extensionality

  _⊸_ : M.ob → M.ob → M.ob
  c ⊸ d = UniversalElement.vertex (cl c d)
