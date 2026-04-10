{-# OPTIONS --lossy-unification #-}
-- Made by Claude
--
-- Experimental variant of Cubical.Categories.Double.Base using primitive
-- whiskering and globular vertical composition, so that the naturality
-- axioms for the unitors and associator become plain equations
--
-- This (and other files with the W suffix) was (were) automatically generated
-- by Claude from their ordinary variants
-- Preliminarily, usage of a primitive whiskering operation does
-- indeed make concrete instantiations easier
-- Compare the naturality proofs in Double.Instances.Prof and Double.Instances.ProfW
-- to see
module Cubical.Categories.Double.BaseW where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

private
  variable
    ℓC ℓV ℓH ℓS : Level

-- A Pseudo Double Category, "whiskered" formulation.
record DoubleCategoryW ℓC ℓH ℓV ℓS :
  Type (ℓ-max (ℓ-suc (ℓ-max (ℓ-max ℓC ℓS) ℓH)) (ℓ-suc ℓV))
  where
  no-eta-equality
  field
    ob : Type ℓC

    -- Strict vertical morphisms
    Homⱽ[_,_] : (x y : ob) → Type ℓV
    idⱽ   : ∀ {x} → Homⱽ[ x , x ]
    _⋆ⱽ_  : ∀ {x y z} (f : Homⱽ[ x , y ]) (g : Homⱽ[ y , z ]) → Homⱽ[ x , z ]
    ⋆ⱽIdL : ∀ {x y} (f : Homⱽ[ x , y ]) → idⱽ ⋆ⱽ f ≡ f
    ⋆ⱽIdR : ∀ {x y} (f : Homⱽ[ x , y ]) → f ⋆ⱽ idⱽ ≡ f
    ⋆ⱽAssoc : ∀ {x y z w} (f : Homⱽ[ x , y ]) (g : Homⱽ[ y , z ])
                          (h : Homⱽ[ z , w ])
           → (f ⋆ⱽ g) ⋆ⱽ h ≡ f ⋆ⱽ (g ⋆ⱽ h)

    -- Weak horizontal morphisms
    Homᴴ[_,_] : (x y : ob) → Type ℓH
    idᴴ   : ∀ {x} → Homᴴ[ x , x ]
    _⋆ᴴ_  : ∀ {x y z} (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) → Homᴴ[ x , z ]

  infixr 9 _⋆ᴴ_
  infixr 9 _⋆ⱽ_

  field
    -- Squares
    Sq : ∀ {x y z w} →
      (fᴴ : Homᴴ[ x , y ]) → (gᴴ : Homᴴ[ z , w ]) →
      (fⱽ : Homⱽ[ x , z ]) → (gⱽ : Homⱽ[ y , w ]) →
      Type ℓS
    isSetSq : ∀ {x y z w}
      {fᴴ : Homᴴ[ x , y ]} {gᴴ : Homᴴ[ z , w ]}
      {fⱽ : Homⱽ[ x , z ]} {gⱽ : Homⱽ[ y , w ]}
      → isSet (Sq fᴴ gᴴ fⱽ gⱽ)

  -- Globular Squares
  GlobSq : ∀ {x y} → (f g : Homᴴ[ x , y ]) → Type ℓS
  GlobSq f g = Sq f g idⱽ idⱽ

  field
    idⱽSq : ∀ {x y} → {h : Homᴴ[ x , y ]} → GlobSq h h
    idᴴSq : ∀ {x y} → {v : Homⱽ[ x , y ]} → Sq idᴴ idᴴ v v

    -- Strict vertical composition of squares
    _⋆ⱽSq_ : ∀ {l1 r1 l2 r2 l3 r3}
        {↑f : Homᴴ[ l1 , r1 ]} {←f : Homⱽ[ l1 , l2 ]} {↓f : Homᴴ[ l2 , r2 ]}
        {→f : Homⱽ[ r1 , r2 ]} {←f' : Homⱽ[ l2 , l3 ]}
        {↓f' : Homᴴ[ l3 , r3 ]} {→f' : Homⱽ[ r2 , r3 ]} →
      Sq ↑f ↓f ←f →f →
      Sq ↓f ↓f' ←f' →f' →
      Sq ↑f ↓f' (←f ⋆ⱽ ←f') (→f ⋆ⱽ →f')

    ⋆ⱽIdLSq : ∀ {u1 u2 d1 d2}
        {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]}
        {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]} →
        (α : Sq ↑f ↓f ←f →f) →
        PathP (λ i → Sq ↑f ↓f (⋆ⱽIdL ←f i) (⋆ⱽIdL →f i)) (idⱽSq ⋆ⱽSq α) α

    ⋆ⱽIdRSq : ∀ {u1 u2 d1 d2}
        {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]}
        {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]} →
        (α : Sq ↑f ↓f ←f →f) →
        PathP (λ i → Sq ↑f ↓f (⋆ⱽIdR ←f i) (⋆ⱽIdR →f i)) (α ⋆ⱽSq idⱽSq) α

    ⋆ⱽAssocSq : ∀ {l1 r1 l2 r2 r3 r4 l3 l4}
        {↑f : Homᴴ[ l1 , r1 ]} {←f : Homⱽ[ l1 , l2 ]}
        {↓f : Homᴴ[ l2 , r2 ]} {→f : Homⱽ[ r1 , r2 ]}
        {↑f' : Homᴴ[ l3 , r3 ]} {←f' : Homⱽ[ l3 , l4 ]}
        {↓f' : Homᴴ[ l4 , r4 ]} {→f' : Homⱽ[ r3 , r4 ]}
        {←f'' : Homⱽ[ l2 , l3 ]}{→f'' : Homⱽ[ r2 , r3 ]} →
        (α : Sq ↑f ↓f ←f →f) → (β : Sq ↓f ↑f' ←f'' →f'') →
        (γ : Sq ↑f' ↓f' ←f' →f') →
        PathP (λ i → Sq ↑f ↓f' (⋆ⱽAssoc ←f ←f'' ←f' i)
                                 (⋆ⱽAssoc →f →f'' →f' i))
          ((α ⋆ⱽSq β) ⋆ⱽSq γ) (α ⋆ⱽSq (β ⋆ⱽSq γ))

    -- Weak horizontal composition of squares
    _⋆ᴴSq_ : ∀ {u1 u2 d1 d2 u3 d3}
        {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]}
        {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]}
        {↑f' : Homᴴ[ u2 , u3 ]} {↓f' : Homᴴ[ d2 , d3 ]}
        {→f' : Homⱽ[ u3 , d3 ]} →
      Sq ↑f ↓f ←f →f →
      Sq ↑f' ↓f' →f →f' →
      Sq (↑f ⋆ᴴ ↑f') (↓f ⋆ᴴ ↓f') ←f →f'

  infixr 9 _⋆ᴴSq_
  infixr 9 _⋆ⱽSq_

  ----------------------------------------------------------------------
  -- Whiskering primitives.
  --
  -- These are the key ingredients that let us state naturality of the
  -- unitors and associator without a PathP base path.  Whiskering a
  -- globular cell onto an ordinary square along a shared horizontal
  -- edge produces a square whose vertical edges are *definitionally*
  -- the original ones, rather than `v ⋆ⱽ idⱽ` or `idⱽ ⋆ⱽ v`.
  ----------------------------------------------------------------------
  field
    -- Right whiskering: paste a globular cell below, keeping the outer
    -- vertical edges.
    _◃_ : ∀ {x y z w}
          {f : Homᴴ[ x , y ]} {g h : Homᴴ[ z , w ]}
          {v : Homⱽ[ x , z ]} {u : Homⱽ[ y , w ]} →
          Sq f g v u → GlobSq g h → Sq f h v u

    -- Left whiskering: paste a globular cell above, keeping the outer
    -- vertical edges.
    _▹_ : ∀ {x y z w}
          {f g : Homᴴ[ x , y ]} {h : Homᴴ[ z , w ]}
          {v : Homⱽ[ x , z ]} {u : Homⱽ[ y , w ]} →
          GlobSq f g → Sq g h v u → Sq f h v u

    -- Globular vertical composition: two globular cells compose to a
    -- globular cell with *definitional* identity vertical edges.
    _⊙ⱽ_ : ∀ {x y} {f g h : Homᴴ[ x , y ]} →
           GlobSq f g → GlobSq g h → GlobSq f h

  infixr 9 _◃_
  infixr 9 _▹_
  infixr 9 _⊙ⱽ_

  field
    -- Coherences relating the new primitives to ⋆ⱽSq.  These *do* have
    -- PathP bases, but each base is a single unitor — NOT a composite
    -- path like ⋆ⱽIdR v ∙ sym (⋆ⱽIdL v).  And they are stated only
    -- once, here in the record, rather than at every naturality site.
    ◃≡⋆ⱽSq : ∀ {x y z w}
          {f : Homᴴ[ x , y ]} {g h : Homᴴ[ z , w ]}
          {v : Homⱽ[ x , z ]} {u : Homⱽ[ y , w ]}
          (α : Sq f g v u) (β : GlobSq g h) →
          PathP (λ i → Sq f h (⋆ⱽIdR v i) (⋆ⱽIdR u i))
                (α ⋆ⱽSq β) (α ◃ β)

    ▹≡⋆ⱽSq : ∀ {x y z w}
          {f g : Homᴴ[ x , y ]} {h : Homᴴ[ z , w ]}
          {v : Homⱽ[ x , z ]} {u : Homⱽ[ y , w ]}
          (α : GlobSq f g) (β : Sq g h v u) →
          PathP (λ i → Sq f h (⋆ⱽIdL v i) (⋆ⱽIdL u i))
                (α ⋆ⱽSq β) (α ▹ β)

    ⊙ⱽ≡⋆ⱽSq : ∀ {x y} {f g h : Homᴴ[ x , y ]}
          (α : GlobSq f g) (β : GlobSq g h) →
          PathP (λ i → Sq f h (⋆ⱽIdR (idⱽ {x = x}) i)
                                (⋆ⱽIdR (idⱽ {x = y}) i))
                (α ⋆ⱽSq β) (α ⊙ⱽ β)

  ----------------------------------------------------------------------
  -- Unitors, associator, and their naturality -- now plain equations.
  ----------------------------------------------------------------------
  field
    -- Left unitor
    λᴴ : ∀ {x y} (f : Homᴴ[ x , y ]) → GlobSq (idᴴ ⋆ᴴ f) f
    λᴴ⁻ : ∀ {x y} (f : Homᴴ[ x , y ]) → GlobSq f (idᴴ ⋆ᴴ f)
    λᴴλᴴ⁻ : ∀ {x y} (f : Homᴴ[ x , y ]) → λᴴ f ⊙ⱽ λᴴ⁻ f ≡ idⱽSq
    λᴴ⁻λᴴ : ∀ {x y} (f : Homᴴ[ x , y ]) → λᴴ⁻ f ⊙ⱽ λᴴ f ≡ idⱽSq
    λᴴ-nat : ∀ {x y z w} {f : Homᴴ[ x , y ]} {g : Homᴴ[ z , w ]}
               {v : Homⱽ[ x , z ]} {u : Homⱽ[ y , w ]} (α : Sq f g v u) →
      (idᴴSq ⋆ᴴSq α) ◃ λᴴ g ≡ λᴴ f ▹ α

    -- Right unitor
    ρᴴ : ∀ {x y} (f : Homᴴ[ x , y ]) → GlobSq (f ⋆ᴴ idᴴ) f
    ρᴴ⁻ : ∀ {x y} (f : Homᴴ[ x , y ]) → GlobSq f (f ⋆ᴴ idᴴ)
    ρᴴρᴴ⁻ : ∀ {x y} (f : Homᴴ[ x , y ]) → ρᴴ f ⊙ⱽ ρᴴ⁻ f ≡ idⱽSq
    ρᴴ⁻ρᴴ : ∀ {x y} (f : Homᴴ[ x , y ]) → ρᴴ⁻ f ⊙ⱽ ρᴴ f ≡ idⱽSq
    ρᴴ-nat : ∀ {x y z w} {f : Homᴴ[ x , y ]} {g : Homᴴ[ z , w ]}
               {v : Homⱽ[ x , z ]} {u : Homⱽ[ y , w ]} (α : Sq f g v u) →
      (α ⋆ᴴSq idᴴSq) ◃ ρᴴ g ≡ ρᴴ f ▹ α

    -- Associator
    αᴴ : ∀ {x y z w}
      (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) (h : Homᴴ[ z , w ])
           → GlobSq ((f ⋆ᴴ g) ⋆ᴴ h) (f ⋆ᴴ (g ⋆ᴴ h))
    αᴴ⁻ : ∀ {x y z w}
      (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) (h : Homᴴ[ z , w ])
           → GlobSq (f ⋆ᴴ (g ⋆ᴴ h)) ((f ⋆ᴴ g) ⋆ᴴ h)
    αᴴαᴴ⁻ : ∀ {x y z w}
      (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) (h : Homᴴ[ z , w ]) →
      αᴴ f g h ⊙ⱽ αᴴ⁻ f g h ≡ idⱽSq
    αᴴ⁻αᴴ : ∀ {x y z w}
      (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) (h : Homᴴ[ z , w ]) →
      αᴴ⁻ f g h ⊙ⱽ αᴴ f g h ≡ idⱽSq
    αᴴ-nat : ∀ {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄}
      {f₁ : Homᴴ[ x₁ , x₂ ]} {f₂ : Homᴴ[ x₂ , x₃ ]} {f₃ : Homᴴ[ x₃ , x₄ ]}
      {g₁ : Homᴴ[ y₁ , y₂ ]} {g₂ : Homᴴ[ y₂ , y₃ ]} {g₃ : Homᴴ[ y₃ , y₄ ]}
      {v₁ : Homⱽ[ x₁ , y₁ ]} {v₂ : Homⱽ[ x₂ , y₂ ]}
      {v₃ : Homⱽ[ x₃ , y₃ ]} {v₄ : Homⱽ[ x₄ , y₄ ]}
      (α₁ : Sq f₁ g₁ v₁ v₂) (α₂ : Sq f₂ g₂ v₂ v₃) (α₃ : Sq f₃ g₃ v₃ v₄) →
      ((α₁ ⋆ᴴSq α₂) ⋆ᴴSq α₃) ◃ αᴴ g₁ g₂ g₃
      ≡ αᴴ f₁ f₂ f₃ ▹ (α₁ ⋆ᴴSq (α₂ ⋆ᴴSq α₃))

    -- Coherence
    pentagon : ∀ {v w x y z}
      (f : Homᴴ[ v , w ]) (g : Homᴴ[ w , x ])
      (h : Homᴴ[ x , y ]) (k : Homᴴ[ y , z ]) →
      αᴴ (f ⋆ᴴ g) h k ⊙ⱽ αᴴ f g (h ⋆ᴴ k)
      ≡ (αᴴ f g h ⋆ᴴSq idⱽSq) ⊙ⱽ αᴴ f (g ⋆ᴴ h) k ⊙ⱽ (idⱽSq ⋆ᴴSq αᴴ g h k)

    triangle : ∀ {x y z} (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) →
      αᴴ f idᴴ g ⊙ⱽ (idⱽSq ⋆ᴴSq λᴴ g) ≡ ρᴴ f ⋆ᴴSq idⱽSq

    interchange : ∀ {u1 u2 u3 m1 m2 m3 d1 d2 d3}
        {↑f : Homᴴ[ u1 , u2 ]} {↑f' : Homᴴ[ u2 , u3 ]}
        {↓f : Homᴴ[ d1 , d2 ]} {↓f' : Homᴴ[ d2 , d3 ]}
        {←f : Homⱽ[ u1 , m1 ]} {←f' : Homⱽ[ m1 , d1 ]}
        {→f : Homⱽ[ u3 , m3 ]} {→f' : Homⱽ[ m3 , d3 ]}
        {←g : Homᴴ[ m1 , m2 ]} {↑g : Homⱽ[ u2 , m2 ]}
        {→g : Homᴴ[ m2 , m3 ]} {↓g : Homⱽ[ m2 , d2 ]}
        (ul : Sq ↑f ←g ←f ↑g) (ur : Sq ↑f' →g ↑g →f)
        (dl : Sq ←g ↓f ←f' ↓g) (dr : Sq →g ↓f' ↓g →f') →
        (ul ⋆ⱽSq dl) ⋆ᴴSq (ur ⋆ⱽSq dr) ≡ (ul ⋆ᴴSq ur) ⋆ⱽSq (dl ⋆ᴴSq dr)
