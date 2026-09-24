{-
  A port of the useful subset of
  `Categories.Category.Monoidal.Reasoning` from agda-categories to
  Cubical. All names are as in agda-categories, but composition is
  diagrammatic (`_⋆_`, "first then"), so a `_∘_`-shape from the
  original translates by reversing the order.

  Conventions
  -----------
  * ⟨_⟩⊗⟨_⟩ and its refl-partial variants are the cong-shortcuts for
    the tensor.
  * split*/merge* rewrite one factor of a tensor as a ⋆-composite (or
    fuse a ⋆-composite of tensors back into one tensor); the digit `1`
    or `2` names which tensor factor is being split, and the ˡ/ʳ names
    which ⋆-factor of the result receives the identity morphism
    (matching agda-categories's convention).
  * serialize converts `f ⊗ g` into the sequential form
    `(f ⊗ id) ⋆ (id ⊗ g)` (or the mirrored order).
-}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_,_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Monoidal.Base

module Cubical.Categories.Monoidal.Reasoning
  {ℓ ℓ'} (M : MonoidalCategory ℓ ℓ') where

open MonoidalCategory M

private variable
  a a' a'' b b' b'' : ob
  f f' : C [ a , a' ]
  g g' : C [ b , b' ]

-- Congruence for _⊗ₕ_.
⊗-resp-≡ : f ≡ f' → g ≡ g' → f ⊗ₕ g ≡ f' ⊗ₕ g'
⊗-resp-≡ p q = cong₂ _⊗ₕ_ p q

⊗-resp-≡ˡ : f ≡ f' → f ⊗ₕ g ≡ f' ⊗ₕ g
⊗-resp-≡ˡ p = cong (_⊗ₕ _) p

⊗-resp-≡ʳ : g ≡ g' → f ⊗ₕ g ≡ f ⊗ₕ g'
⊗-resp-≡ʳ q = cong (_ ⊗ₕ_) q

infixr 6 ⟨_⟩⊗⟨_⟩ refl⟩⊗⟨_
infixl 7 _⟩⊗⟨refl

⟨_⟩⊗⟨_⟩ : f ≡ f' → g ≡ g' → f ⊗ₕ g ≡ f' ⊗ₕ g'
⟨ p ⟩⊗⟨ q ⟩ = ⊗-resp-≡ p q

refl⟩⊗⟨_ : g ≡ g' → f ⊗ₕ g ≡ f ⊗ₕ g'
refl⟩⊗⟨_ = ⊗-resp-≡ʳ

_⟩⊗⟨refl : f ≡ f' → f ⊗ₕ g ≡ f' ⊗ₕ g
_⟩⊗⟨refl = ⊗-resp-≡ˡ


-- Bifunctoriality (⊗ preserves ⋆).
--   (f ⋆ f') ⊗ (g ⋆ g') ≡ (f ⊗ g) ⋆ (f' ⊗ g')
⊗-distrib-over-⋆ :
    {f : C [ a , a' ]} {f' : C [ a' , a'' ]}
    {g : C [ b , b' ]} {g' : C [ b' , b'' ]}
  → (f ⋆ f') ⊗ₕ (g ⋆ g') ≡ (f ⊗ₕ g) ⋆ (f' ⊗ₕ g')
⊗-distrib-over-⋆ {f = f} {f'} {g} {g'} =
  Functor.F-seq ─⊗─ (f , g) (f' , g')

-- ⊗ preserves id.
⊗-id : ∀ {a b} → id {a} ⊗ₕ id {b} ≡ id
⊗-id = Functor.F-id ─⊗─


-- Split composites within a single tensor factor.
-- In `split₁ᵢ`, the composite (f ⋆ g) appears in the first ⊗-factor;
-- the id ends up in the "ˡ" or "ʳ" ⋆-factor of the resulting composite.

module _ {a a' a'' b b'}
  {f : C [ a , a' ]} {g : C [ a' , a'' ]}
  {h : C [ b , b' ]} where

  split₁ˡ : (f ⋆ g) ⊗ₕ h ≡ (f ⊗ₕ id) ⋆ (g ⊗ₕ h)
  split₁ˡ =
    ⟨ refl ⟩⊗⟨ sym (⋆IdL h) ⟩ ∙ ⊗-distrib-over-⋆

  split₁ʳ : (f ⋆ g) ⊗ₕ h ≡ (f ⊗ₕ h) ⋆ (g ⊗ₕ id)
  split₁ʳ =
    ⟨ refl ⟩⊗⟨ sym (⋆IdR h) ⟩ ∙ ⊗-distrib-over-⋆

module _ {a a' b b' b''}
  {f : C [ a , a' ]}
  {g : C [ b , b' ]} {h : C [ b' , b'' ]} where

  split₂ˡ : f ⊗ₕ (g ⋆ h) ≡ (id ⊗ₕ g) ⋆ (f ⊗ₕ h)
  split₂ˡ =
    ⟨ sym (⋆IdL f) ⟩⊗⟨ refl ⟩ ∙ ⊗-distrib-over-⋆

  split₂ʳ : f ⊗ₕ (g ⋆ h) ≡ (f ⊗ₕ g) ⋆ (id ⊗ₕ h)
  split₂ʳ =
    ⟨ sym (⋆IdR f) ⟩⊗⟨ refl ⟩ ∙ ⊗-distrib-over-⋆


-- Merges are the inverses of the splits: fuse a ⋆-composite of two
-- tensors (with an id in one corner) back into a single tensor.

module _ {a a' a'' b b'}
  {f : C [ a , a' ]} {g : C [ a' , a'' ]}
  {h : C [ b , b' ]} where

  merge₁ˡ : (f ⊗ₕ id) ⋆ (g ⊗ₕ h) ≡ (f ⋆ g) ⊗ₕ h
  merge₁ˡ = sym split₁ˡ

  merge₁ʳ : (f ⊗ₕ h) ⋆ (g ⊗ₕ id) ≡ (f ⋆ g) ⊗ₕ h
  merge₁ʳ = sym split₁ʳ

module _ {a a' b b' b''}
  {f : C [ a , a' ]}
  {g : C [ b , b' ]} {h : C [ b' , b'' ]} where

  merge₂ˡ : (id ⊗ₕ g) ⋆ (f ⊗ₕ h) ≡ f ⊗ₕ (g ⋆ h)
  merge₂ˡ = sym split₂ˡ

  merge₂ʳ : (f ⊗ₕ g) ⋆ (id ⊗ₕ h) ≡ f ⊗ₕ (g ⋆ h)
  merge₂ʳ = sym split₂ʳ


-- Serialize a parallel tensor as a sequential one.

serialize₁₂ : {f : C [ a , a' ]} {g : C [ b , b' ]}
            → f ⊗ₕ g ≡ (f ⊗ₕ id) ⋆ (id ⊗ₕ g)
serialize₁₂ {f = f} {g} =
  ⟨ sym (⋆IdR f) ⟩⊗⟨ sym (⋆IdL g) ⟩ ∙ ⊗-distrib-over-⋆

serialize₂₁ : {f : C [ a , a' ]} {g : C [ b , b' ]}
            → f ⊗ₕ g ≡ (id ⊗ₕ g) ⋆ (f ⊗ₕ id)
serialize₂₁ {f = f} {g} =
  ⟨ sym (⋆IdL f) ⟩⊗⟨ sym (⋆IdR g) ⟩ ∙ ⊗-distrib-over-⋆
