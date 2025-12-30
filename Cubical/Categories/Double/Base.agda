module Cubical.Categories.Double.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓV ℓH : Level

-- A Pseudo Double Category
record DoubleCategory ℓC ℓH ℓV ℓS :
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
    ⋆ⱽAssoc : ∀ {x y z w} (f : Homⱽ[ x , y ]) (g : Homⱽ[ y , z ]) (h : Homⱽ[ z , w ])
           → (f ⋆ⱽ g) ⋆ⱽ h ≡ f ⋆ⱽ (g ⋆ⱽ h)
    isSetHomⱽ : ∀ {x y} → isSet Homⱽ[ x , y ]

    -- Weak horizontal morphisms
    Homᴴ[_,_] : (x y : ob) → Type ℓH
    idᴴ   : ∀ {x} → Homᴴ[ x , x ]
    _⋆ᴴ_  : ∀ {x y z} →
      (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) → Homᴴ[ x , z ]
    isSetHomᴴ : ∀ {x y} → isSet Homᴴ[ x , y ]

  infixr 9 _⋆ᴴ_
  infixr 9 _⋆ⱽ_

  field
    -- Squares
    Sq : ∀ {x y z w} →
      (fᴴ : Homᴴ[ x , y ]) → (gᴴ : Homᴴ[ z , w ]) →
      (fⱽ : Homⱽ[ x , z ]) → (gⱽ : Homⱽ[ y , w ]) →
      Type ℓS

  -- Globular Squares
  GlobSq : ∀ {x y} → (f g : Homᴴ[ x , y ]) → Type ℓS
  GlobSq f g = Sq f g idⱽ idⱽ

  field
    idⱽSq : ∀ {x y} → {h : Homᴴ[ x , y ]} → Sq h h idⱽ idⱽ
    idᴴSq : ∀ {x y} → {v : Homⱽ[ x , y ]} → Sq idᴴ idᴴ v v

    -- Strict vertical composition of squares
    _⋆ⱽSq_ : ∀ {l1 r1 l2 r2 l3 r3}
        {↑f : Homᴴ[ l1 , r1 ]} {←f : Homⱽ[ l1 , l2 ]} {↓f : Homᴴ[ l2 , r2 ]}
        {→f : Homⱽ[ r1 , r2 ]} {←f' : Homⱽ[ l2 , l3 ]} {↓f' : Homᴴ[ l3 , r3 ]} {→f' : Homⱽ[ r2 , r3 ]} →
      Sq ↑f ↓f ←f →f →
      Sq ↓f ↓f' ←f' →f' →
      Sq ↑f ↓f' (←f ⋆ⱽ ←f') (→f ⋆ⱽ →f')

    ⋆ⱽIdLSq : ∀ {u1 u2 d1 d2}
        {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]} {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]} →
        (α : Sq ↑f ↓f ←f →f) →
        PathP (λ i → Sq ↑f ↓f (⋆ⱽIdL ←f i) (⋆ⱽIdL →f i)) (idⱽSq ⋆ⱽSq α) α

    ⋆ⱽIdRSq : ∀ {u1 u2 d1 d2}
        {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]} {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]} →
        (α : Sq ↑f ↓f ←f →f) →
        PathP (λ i → Sq ↑f ↓f (⋆ⱽIdR ←f i) (⋆ⱽIdR →f i)) (α ⋆ⱽSq idⱽSq) α

    ⋆ⱽAssocSq : ∀ {l1 r1 l2 r2 r3 r4 l3 l4}
        {↑f : Homᴴ[ l1 , r1 ]} {←f : Homⱽ[ l1 , l2 ]} {↓f : Homᴴ[ l2 , r2 ]} {→f : Homⱽ[ r1 , r2 ]}
        {↑f' : Homᴴ[ l3 , r3 ]} {←f' : Homⱽ[ l3 , l4 ]} {↓f' : Homᴴ[ l4 , r4 ]} {→f' : Homⱽ[ r3 , r4 ]}
        {←f'' : Homⱽ[ l2 , l3 ]}{→f'' : Homⱽ[ r2 , r3 ]} →
        (α : Sq ↑f ↓f ←f →f) → (β : Sq ↓f ↑f' ←f'' →f'') → (γ : Sq ↑f' ↓f' ←f' →f') →
        PathP (λ i → Sq ↑f ↓f' (⋆ⱽAssoc ←f ←f'' ←f' i) (⋆ⱽAssoc →f →f'' →f' i))
          ((α ⋆ⱽSq β) ⋆ⱽSq γ) (α ⋆ⱽSq (β ⋆ⱽSq γ))

    -- Weak horizontal composition of squares
    _⋆ᴴSq_ : ∀ {u1 u2 d1 d2 u3 d3}
        {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]} {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]}
        {↑f' : Homᴴ[ u2 , u3 ]} {↓f' : Homᴴ[ d2 , d3 ]} {→f' : Homⱽ[ u3 , d3 ]} →
      Sq ↑f ↓f ←f →f →
      Sq ↑f' ↓f' →f →f' →
      Sq (↑f ⋆ᴴ ↑f') (↓f ⋆ᴴ ↓f') ←f →f'

    -- ⋆ᴴAssocSq : ∀ {u1 u2 d1 d2 u4 d3 u3 d4}
    --     {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]} {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]}
    --     {↑f' : Homᴴ[ u3 , u4 ]} {←f' : Homⱽ[ u3 , d4 ]} {↓f' : Homᴴ[ d4 , d3 ]} {→f' : Homⱽ[ u4 , d3 ]}
    --     {↑f'' : Homᴴ[ u2 , u3 ]}{↓f'' : Homᴴ[ d2 , d4 ]} →
    --     (α : Sq ↑f ↓f ←f →f) → (β : Sq ↑f'' ↓f'' →f ←f') → (γ : Sq ↑f' ↓f' ←f' →f') →
    --     PathP (λ i → Sq (⋆ᴴAssoc ↑f ↑f'' ↑f' i) (⋆ᴴAssoc ↓f ↓f'' ↓f' i) ←f →f')
    --       ((α ⋆ᴴSq β) ⋆ᴴSq γ) (α ⋆ᴴSq (β ⋆ᴴSq γ))


  infixr 9 _⋆ᴴSq_
  infixr 9 _⋆ⱽSq_

  field
    -- left unitor
    λᴴ : ∀ {x y} (f : Homᴴ[ x , y ]) → GlobSq (idᴴ ⋆ᴴ f) f
    λᴴ⁻ : ∀ {x y} (f : Homᴴ[ x , y ]) → GlobSq f (idᴴ ⋆ᴴ f)
    λᴴλᴴ⁻ : ∀ {x y} (f : Homᴴ[ x , y ]) →
      PathP (λ i → Sq (idᴴ ⋆ᴴ f) (idᴴ ⋆ᴴ f) (⋆ⱽIdL idⱽ i) (⋆ⱽIdL idⱽ i))
        (λᴴ f ⋆ⱽSq λᴴ⁻ f) idⱽSq
    λᴴ⁻λᴴ : ∀ {x y} (f : Homᴴ[ x , y ]) →
      PathP (λ i → Sq f f (⋆ⱽIdL idⱽ i) (⋆ⱽIdL idⱽ i))
        (λᴴ⁻ f ⋆ⱽSq λᴴ f) idⱽSq
    λᴴ-nat : ∀ {x y z w} {f : Homᴴ[ x , y ]} {g : Homᴴ[ z , w ]}
               {v : Homⱽ[ x , z ]} {u : Homⱽ[ y , w ]} (α : Sq f g v u) →
      PathP (λ i → Sq (idᴴ ⋆ᴴ f) g
                     ((⋆ⱽIdR v ∙ sym (⋆ⱽIdL v)) i)
                     ((⋆ⱽIdR u ∙ sym (⋆ⱽIdL u)) i))
             ((idᴴSq ⋆ᴴSq α) ⋆ⱽSq λᴴ g)
             (λᴴ f ⋆ⱽSq α)

    -- right unitor
    ρᴴ : ∀ {x y} (f : Homᴴ[ x , y ]) → GlobSq (f ⋆ᴴ idᴴ) f
    ρᴴ⁻ : ∀ {x y} (f : Homᴴ[ x , y ]) → GlobSq f (f ⋆ᴴ idᴴ)
    ρᴴρᴴ⁻ : ∀ {x y} (f : Homᴴ[ x , y ]) →
      PathP (λ i → Sq (f ⋆ᴴ idᴴ) (f ⋆ᴴ idᴴ) (⋆ⱽIdL idⱽ i) (⋆ⱽIdL idⱽ i))
        (ρᴴ f ⋆ⱽSq ρᴴ⁻ f) idⱽSq
    ρᴴ⁻ρᴴ : ∀ {x y} (f : Homᴴ[ x , y ]) →
      PathP (λ i → Sq f f (⋆ⱽIdL idⱽ i) (⋆ⱽIdL idⱽ i))
        (ρᴴ⁻ f ⋆ⱽSq ρᴴ f) idⱽSq
    ρᴴ-nat : ∀ {x y z w} {f : Homᴴ[ x , y ]} {g : Homᴴ[ z , w ]}
               {v : Homⱽ[ x , z ]} {u : Homⱽ[ y , w ]} (α : Sq f g v u) →
      PathP (λ i → Sq (f ⋆ᴴ idᴴ) g
                     ((⋆ⱽIdR v ∙ sym (⋆ⱽIdL v)) i)
                     ((⋆ⱽIdR u ∙ sym (⋆ⱽIdL u)) i))
             ((α ⋆ᴴSq idᴴSq) ⋆ⱽSq ρᴴ g)
             (ρᴴ f ⋆ⱽSq α)

    -- associator
    αᴴ : ∀ {x y z w}
      (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) (h : Homᴴ[ z , w ])
           → GlobSq ((f ⋆ᴴ g) ⋆ᴴ h) (f ⋆ᴴ (g ⋆ᴴ h))
    αᴴ⁻ : ∀ {x y z w}
      (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) (h : Homᴴ[ z , w ])
           → GlobSq (f ⋆ᴴ (g ⋆ᴴ h)) ((f ⋆ᴴ g) ⋆ᴴ h)
    αᴴαᴴ⁻ : ∀ {x y z w}
      (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) (h : Homᴴ[ z , w ]) →
      PathP (λ i → Sq ((f ⋆ᴴ g) ⋆ᴴ h) ((f ⋆ᴴ g) ⋆ᴴ h) (⋆ⱽIdL idⱽ i) (⋆ⱽIdL idⱽ i))
        (αᴴ f g h ⋆ⱽSq αᴴ⁻ f g h ) idⱽSq
    αᴴ⁻αᴴ : ∀ {x y z w}
      (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) (h : Homᴴ[ z , w ]) →
      PathP (λ i → Sq (f ⋆ᴴ (g ⋆ᴴ h)) (f ⋆ᴴ (g ⋆ᴴ h)) (⋆ⱽIdL idⱽ i) (⋆ⱽIdL idⱽ i))
        (αᴴ⁻ f g h ⋆ⱽSq αᴴ f g h ) idⱽSq
    αᴴ-nat : ∀ {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄}
      {f₁ : Homᴴ[ x₁ , x₂ ]} {f₂ : Homᴴ[ x₂ , x₃ ]} {f₃ : Homᴴ[ x₃ , x₄ ]}
      {g₁ : Homᴴ[ y₁ , y₂ ]} {g₂ : Homᴴ[ y₂ , y₃ ]} {g₃ : Homᴴ[ y₃ , y₄ ]}
      {v₁ : Homⱽ[ x₁ , y₁ ]} {v₂ : Homⱽ[ x₂ , y₂ ]}
      {v₃ : Homⱽ[ x₃ , y₃ ]} {v₄ : Homⱽ[ x₄ , y₄ ]}
      (α₁ : Sq f₁ g₁ v₁ v₂) (α₂ : Sq f₂ g₂ v₂ v₃) (α₃ : Sq f₃ g₃ v₃ v₄) →
      PathP (λ i → Sq ((f₁ ⋆ᴴ f₂) ⋆ᴴ f₃) (g₁ ⋆ᴴ (g₂ ⋆ᴴ g₃))
                      ((⋆ⱽIdR v₁ ∙ sym (⋆ⱽIdL v₁)) i)
                      ((⋆ⱽIdR v₄ ∙ sym (⋆ⱽIdL v₄)) i))
        (((α₁ ⋆ᴴSq α₂) ⋆ᴴSq α₃) ⋆ⱽSq αᴴ g₁ g₂ g₃)
        (αᴴ f₁ f₂ f₃ ⋆ⱽSq (α₁ ⋆ᴴSq (α₂ ⋆ᴴSq α₃)))

    -- Coherence
    pentagon : ∀ {v w x y z}
      (f : Homᴴ[ v , w ]) (g : Homᴴ[ w , x ]) (h : Homᴴ[ x , y ]) (k : Homᴴ[ y , z ]) →
      PathP (λ i → Sq (((f ⋆ᴴ g) ⋆ᴴ h) ⋆ᴴ k) (f ⋆ᴴ (g ⋆ᴴ (h ⋆ᴴ k)))
        (⋆ⱽIdL (idⱽ ⋆ⱽ idⱽ) (~ i))
        (⋆ⱽIdL (idⱽ ⋆ⱽ idⱽ) (~ i)))
        (αᴴ (f ⋆ᴴ g) h k ⋆ⱽSq αᴴ f g (h ⋆ᴴ k))
        ((αᴴ f g h ⋆ᴴSq idⱽSq) ⋆ⱽSq αᴴ f (g ⋆ᴴ h) k ⋆ⱽSq (idⱽSq ⋆ᴴSq αᴴ g h k))

    triangle : ∀ {x y z} (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) →
      PathP (λ i → Sq ((f ⋆ᴴ idᴴ) ⋆ᴴ g) (f ⋆ᴴ g)
                      (⋆ⱽIdL idⱽ i) (⋆ⱽIdL idⱽ i))
        (αᴴ f idᴴ g ⋆ⱽSq (idⱽSq ⋆ᴴSq λᴴ g))
        (ρᴴ f ⋆ᴴSq idⱽSq)

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


--   ⟨_⟩⋆ⱽ⟨_⟩ : ∀ {x y z} {f f' : Homⱽ[ x , y ]} {g g' : Homⱽ[ y , z ]} →
--     f ≡ f' → g ≡ g' → f ⋆ⱽ g ≡ f' ⋆ⱽ g'
--   ⟨ f≡ ⟩⋆ⱽ⟨ g≡ ⟩ = cong₂ _⋆ⱽ_ f≡ g≡

--   ⟨_⟩⋆ᴴ⟨_⟩ : ∀ {x y z} {f f' : Homᴴ[ x , y ]} {g g' : Homᴴ[ y , z ]} →
--       {α α' : Homᴴ[ x , y ]} {β β' : Homᴴ[ y , z ]} →
--       α ≡ α' → β ≡ β' → α ⋆ᴴ β ≡ α' ⋆ᴴ β'
--   ⟨ α≡ ⟩⋆ᴴ⟨ β≡ ⟩ = cong₂ _⋆ᴴ_ α≡ β≡

-- -- open Bifunctor
-- -- open Functor
-- -- -- TODO level polymorphise
-- -- module _ {ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓS ℓR}
-- --   {C : Category ℓC ℓC'}
-- --   {D : Category ℓD ℓD'}
-- --   {E : Category ℓE ℓE'}
-- --   (S : Relatoro* C ℓS D)
-- --   (R : Relatoro* D ℓR E)
-- --   where
-- --   seqRelator : Relatoro* C (ℓ-max (ℓ-max ℓD ℓD') (ℓ-max ℓS ℓR)) E
-- --   seqRelator = ⊗-Bif ∘Flr (CurryBifunctor S , CurryBifunctorL R)

-- --   module _ {c e} where
-- --     test : ⟨ seqRelator .Bif-ob c e ⟩ ≡ (appL S c ⊗ appR R e)
-- --     test = refl

-- -- module _ ℓC ℓC' ℓS {ℓD ℓD' ℓS}
-- --   {C : Category ℓC ℓC'}
-- --   {D : Category ℓD ℓD'}
-- --   (S : Relatoro* C (ℓ-max (ℓ-max ℓC ℓC') ℓS) D)
-- --   where

-- --   open Iso

-- --   private
-- --     IdRelator = (compF (LiftF {ℓ = ℓC'} {ℓ' = ℓ-max ℓS ℓC}) (HomBif C))
-- --     module C = Category C

-- --   module _ c d where
-- --     private
-- --       C⟨c,-⟩* =
-- --         CurryBifunctor (compF (LiftF {ℓ = ℓC'} {ℓ' = ℓ-max ℓS ℓC}) (HomBif C)) .F-ob c
-- --       S⟨-,d⟩ = CurryBifunctorL S .F-ob d

-- --       module C⟨c,-⟩*⊗S⟨-,d⟩ = Tensor C⟨c,-⟩* S⟨-,d⟩

-- --     -- Can I make this follow directly from CoYoneda?
-- --     ⋆SeqRelatorIdLIso :
-- --       Iso ⟨ seqRelator IdRelator S .Bif-ob c d ⟩
-- --           ⟨ S .Bif-ob c d ⟩
-- --     ⋆SeqRelatorIdLIso .fun =
-- --       C⟨c,-⟩*⊗S⟨-,d⟩.rec
-- --         (Bif-ob S c d .snd)
-- --         (λ {x} p → Bif-homL S (p .lower) d)
-- --         (λ _ _ _ → sym $ funExt⁻ (Bif-L-seq S _ _) _)
-- --     ⋆SeqRelatorIdLIso .inv = C⟨c,-⟩*⊗S⟨-,d⟩._,⊗_ (lift (C .Category.id))
-- --     ⋆SeqRelatorIdLIso .rightInv = funExt⁻ (S .Bif-L-id)
-- --     ⋆SeqRelatorIdLIso .leftInv =
-- --       C⟨c,-⟩*⊗S⟨-,d⟩.ind (λ _ → isSet⊗ _ _)
-- --         (λ _ _ → C⟨c,-⟩*⊗S⟨-,d⟩.swap _ _ _ ∙ cong (C⟨c,-⟩*⊗S⟨-,d⟩._,⊗ _)
-- --           (cong lift (C.⋆IdL _)))

-- --   private
-- --     C⟨1,-⟩* : ∀ {c} → Functor C (SET (ℓ-max ℓC' (ℓ-max ℓS ℓC)))
-- --     C⟨1,-⟩* {c} =
-- --       CurryBifunctor (compF (LiftF {ℓ = ℓC'} {ℓ' = ℓ-max ℓS ℓC}) (HomBif C)) .F-ob c
-- --     S⟨-,2⟩ : ∀ {d} → Functor (C ^op) (SET (ℓ-max (ℓ-max ℓC ℓC') ℓS))
-- --     S⟨-,2⟩ {d} = CurryBifunctorL S .F-ob d
-- --     module C⟨1,-⟩*⊗S⟨-,2⟩ {c d} = Tensor (C⟨1,-⟩* {c}) (S⟨-,2⟩ {d})
-- --     module _ c d where
-- --       module Hom⊗S = Tensor (C⟨1,-⟩* {c}) (S⟨-,2⟩ {d})

-- --   opaque
-- --     ⋆SeqRelatorIdL : RelatorIso (seqRelator IdRelator S) S
-- --     ⋆SeqRelatorIdL =
-- --       Isos→PshIso
-- --         (λ (c , d) → ⋆SeqRelatorIdLIso c d)
-- --         (λ (c , d) (c' , d') (f , g) p →
-- --           let module X = Hom⊗S c d in
-- --           let module Y = Hom⊗S c' d' in
-- --           let module Id⋆S = PresheafNotation (Relator→Psh (seqRelator IdRelator S)) in
-- --           Y.ind
-- --             {A = λ q → X.rec _ _ _ ((f , g) Id⋆S.⋆ q) ≡
-- --                        S .Bif-hom× f g (Y.rec _ _ _ q)}
-- --             (λ q → S .Bif-ob _ _ .snd _ _)
-- --             (λ g q →
-- --               funExt⁻ (S .Bif-L-seq _ _) _
-- --               ∙ cong (Bif-homL S f d)
-- --                   (funExt⁻ (S .Bif-RL-fuse _ _) _
-- --                   ∙ (sym $ funExt⁻ (S .Bif-LR-fuse _ _) _))
-- --               ∙ funExt⁻ (S .Bif-RL-fuse _ _) _
-- --             )
-- --             p
-- --           )

-- -- open DoubleCategory
-- -- open PshHom
-- -- open Functor


-- -- -- -- module _
-- -- -- --   {ℓC ℓC' ℓCᴰ ℓCᴰ' ℓP}
-- -- -- --   {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (P : Presheaf C ℓP)
-- -- -- --   where

-- -- module _ {ℓC ℓC'}
-- --   (C : Category ℓC ℓC') (pb : Pullbacks C)
-- --   where
-- --   private
-- --     module C = Category C


-- --   record Span (l r : C.ob) : Type (ℓ-max ℓC ℓC') where
-- --     constructor span
-- --     field
-- --       apex : C.ob
-- --       s₁ : C.Hom[ apex , l ]
-- --       s₂ : C.Hom[ apex , r ]

-- --   idSpan : ∀ {c} → Span c c
-- --   idSpan = span _ C.id C.id

-- --   open Pullback
-- --   open Span

-- --   seqSpan : ∀ {x y z} → Span x y → Span y z → Span x z
-- --   seqSpan {x = x} {y = y} {z = z} r s =
-- --     span (pb (cospan (r .apex) y (s .apex) (r .s₂) (s .s₁)) .pbOb)
-- --       (pb (cospan (r .apex) y (s .apex) (r .s₂) (s .s₁)) .pbPr₁ C.⋆ r .s₁)
-- --       (pb (cospan (r .apex) y (s .apex) (r .s₂) (s .s₁)) .pbPr₂ C.⋆ s .s₂)

-- --   mkSpan≡ : ∀ {x y z} → {f f' : C.Hom[ x , y ]} {g g' : C.Hom[ x , z ]} →
-- --     f ≡ f' →
-- --     g ≡ g' →
-- --     span x f g ≡ span x f' g'
-- --   mkSpan≡ f≡ g≡ = {!!}

-- --   SPAN : DoubleCategory _ _ _ _
-- --   SPAN .ob = C.ob
-- --   SPAN .Homⱽ[_,_] = C.Hom[_,_]
-- --   SPAN .idⱽ = C.id
-- --   SPAN ._⋆ⱽ_ = C._⋆_
-- --   SPAN .⋆ⱽIdL = C.⋆IdL
-- --   SPAN .⋆ⱽIdR = C.⋆IdR
-- --   SPAN .⋆ⱽAssoc = C.⋆Assoc
-- --   SPAN .Homᴴ[_,_] = Span
-- --   SPAN .idᴴ = idSpan
-- --   SPAN ._⋆ᴴ_ = seqSpan
-- --   --
-- --   --      .
-- --   --     / \
-- --   --    x   s
-- --   --   / \ / \
-- --   --  x   x   y
-- --   SPAN .⋆ᴴIdL s =
-- --     {!!}
-- --   SPAN .⋆ᴴIdR = {!!}
-- --   SPAN .⋆ᴴAssoc = {!!}
-- --   SPAN .isSetHomᴴ = {!!}
-- --   SPAN .Sq = {!!}
-- --   SPAN .idⱽSq = {!!}
-- --   SPAN .idᴴSq = {!!}
-- --   SPAN ._⋆ⱽSq_ = {!!}
-- --   SPAN .⋆ⱽIdLSq = {!!}
-- --   SPAN .⋆ⱽIdRSq = {!!}
-- --   SPAN ._⋆ᴴSq_ = {!!}
-- --   SPAN .⋆ᴴIdLSq = {!!}
-- --   SPAN .⋆ᴴIdRSq = {!!}
-- --   SPAN .⋆ⱽAssocSq = {!!}
-- --   SPAN .⋆ᴴAssocSq = {!!}
-- --   SPAN .interchange = {!!}


-- -- -- module _ {ℓC ℓC' ℓS} where
-- -- --   PROF : DoubleCategory _ _ _ ℓS
-- -- --   PROF .ob = Category ℓC ℓC'
-- -- --   PROF .Homⱽ[_,_] = Functor
-- -- --   PROF .idⱽ = Id
-- -- --   PROF ._⋆ⱽ_ G F = F ∘F G
-- -- --   PROF .⋆ⱽIdL _ = F-lUnit
-- -- --   PROF .⋆ⱽIdR _ = F-rUnit
-- -- --   PROF .⋆ⱽAssoc _ _ _ = F-assoc
-- -- --   PROF .Homᴴ[_,_] C D =
-- -- --     Relatoro* C (ℓ-max ℓS (ℓ-max ℓC ℓC')) D
-- -- --   PROF .idᴴ {x = C} = compF (LiftF {ℓ = ℓC'} {ℓ' = ℓ-max ℓS ℓC}) (HomBif C)
-- -- --   PROF ._⋆ᴴ_ S R = seqRelator S R
-- -- --   PROF .⋆ᴴIdL {x = C} S = RelatorIso→Path {!⋆SeqRelatorIdL ℓC ℓC' ℓS {C = C} S!}
-- -- --   PROF .⋆ᴴIdR = {!!}
-- -- --   PROF .⋆ᴴAssoc = {!!}
-- -- --   PROF .isSetHomᴴ = {!!}
-- -- --   PROF .Sq = {!!}
-- -- --   PROF .idⱽSq = {!!}
-- -- --   PROF .idᴴSq = {!!}
-- -- --   PROF ._⋆ⱽSq_ = {!!}
-- -- --   PROF .⋆ⱽIdLSq = {!!}
-- -- --   PROF .⋆ⱽIdRSq = {!!}
-- -- --   PROF ._⋆ᴴSq_ = {!!}
-- -- --   PROF .⋆ᴴIdLSq = {!!}
-- -- --   PROF .⋆ᴴIdRSq = {!!}
-- -- --   PROF .⋆ⱽAssocSq = {!!}
-- -- --   PROF .⋆ᴴAssocSq = {!!}
-- -- --   PROF .interchange = {!!}

-- -- --   -- PROF .ob = Category ℓC ℓC'
-- -- --   -- PROF .Homⱽ[_,_] = Functor
-- -- --   -- PROF .idⱽ = Id
-- -- --   -- PROF ._⋆ⱽ_ G F = F ∘F G
-- -- --   -- PROF .⋆ⱽIdL _ = F-lUnit
-- -- --   -- PROF .⋆ⱽIdR _ = F-rUnit
-- -- --   -- PROF .⋆ⱽAssoc _ _ _ = F-assoc
-- -- --   -- PROF .Homᴴ[_,_] C D = Relatoro* C (ℓ-max (ℓ-max ℓC ℓC') ℓS) D
-- -- --   -- PROF .idᴴ {x = C} = {!HomBif C!}
-- -- --   -- -- compF (LiftF {ℓ = ℓC'} {ℓ' = ℓ-max ℓC ℓS}) (HomBif C)
-- -- --   -- PROF ._⋆ᴴ_ S R = seqRelator S R
-- -- --   -- -- TODO show these are iso then use univalence
-- -- --   -- PROF .⋆ᴴIdL S = {!!}
-- -- --   -- PROF .⋆ᴴIdR S = {!!}
-- -- --   -- PROF .⋆ᴴAssoc = {!!}
-- -- --   -- PROF .isSetHomᴴ = {!!}
-- -- --   -- PROF .Sq S R F G = RelatorHom S (R ∘Flr ((F ^opF) , G))
-- -- --   -- PROF .idⱽSq = eqToPshHom _ Eq.refl Eq.refl
-- -- --   -- PROF .idᴴSq {v = F} = {!!}
-- -- --   --   -- mkRelatorHom (λ c d z → lift (F .Functor.F-hom (z .lower)))
-- -- --   --   --   (λ _ _ _ _ _ → cong lift (F .F-seq _ _))
-- -- --   --   --   (λ _ _ _ _ _ → cong lift (F .F-seq _ _))
-- -- --   -- PROF ._⋆ⱽSq_ {↑f = ↑f} {→f = →f} {↓f' = ↓f'} {→f' = →f'} α β =
-- -- --   --   {!!}
-- -- --   --   -- mkRelatorHom (λ c d z → β .N-ob _ (α .N-ob (c , d) z))
-- -- --   --   --   (λ c c' d f p →
-- -- --   --   --     cong (β .N-ob _) (cong (α .N-ob (c , d)) (funExt⁻ (↑f .Bif-L×-agree f) p ) ∙ α .N-hom _ _ _ _)
-- -- --   --   --     ∙ β .N-hom _ _ _ _
-- -- --   --   --     ∙ funExt⁻ (cong₂ (↓f' .Bif-hom×) refl (cong (→f' .F-hom) (→f .F-id) ∙ →f' .F-id)) _
-- -- --   --   --     ∙ (sym $ funExt⁻ (↓f' .Bif-L×-agree _) _))
-- -- --   --   --   {!!}
-- -- --   -- PROF .⋆ⱽIdLSq α = {!!}
-- -- --   -- PROF .⋆ⱽIdRSq = {!!}
-- -- --   -- PROF ._⋆ᴴSq_ = {!!}
-- -- --   -- PROF .⋆ᴴIdLSq = {!!}
-- -- --   -- PROF .⋆ᴴIdRSq = {!!}
-- -- --   -- PROF .⋆ⱽAssocSq = {!!}
-- -- --   -- PROF .⋆ᴴAssocSq = {!!}
-- -- --   -- PROF .interchange = {!!}

-- -- -- -- -- -- -- module _ {ℓC ℓC'} where
-- -- -- -- -- -- --   CAT : 2Category _ _ _
-- -- -- -- -- -- --   CAT .ob = GroupoidObjectsCategory ℓC ℓC'
-- -- -- -- -- -- --   CAT .Hom₁[_,_] C D = Functor (C .cat) (D .cat)
-- -- -- -- -- -- --   CAT .Hom₂[_,_] = NatTrans
-- -- -- -- -- -- --   CAT .id₁ = Id
-- -- -- -- -- -- --   CAT .id₂ = idTrans _
-- -- -- -- -- -- --   CAT ._⋆₁_ F G = G ∘F F
-- -- -- -- -- -- --   CAT ._⋆ⱽ_ = seqTrans
-- -- -- -- -- -- --   CAT ._⋆ᴴ_ α β = whiskerTrans β α
-- -- -- -- -- -- --   CAT .⋆₁IdL F = F-lUnit
-- -- -- -- -- -- --   CAT .⋆₁IdR F = F-rUnit
-- -- -- -- -- -- --   CAT .⋆₁Assoc _ _ _ = F-assoc
-- -- -- -- -- -- --   CAT .⋆ⱽIdL {y = D} α =
-- -- -- -- -- -- --     makeNatTransPath (funExt λ _ → D.⋆IdL _ )
-- -- -- -- -- -- --     where module D = GroupoidObjectsCategory D
-- -- -- -- -- -- --   CAT .⋆ⱽIdR {y = D} α =
-- -- -- -- -- -- --     makeNatTransPath (funExt λ _ → D.⋆IdR _ )
-- -- -- -- -- -- --     where module D = GroupoidObjectsCategory D
-- -- -- -- -- -- --   CAT .⋆ⱽAssoc {y = D} _ _ _ =
-- -- -- -- -- -- --     makeNatTransPath (funExt λ _ → D.⋆Assoc _ _ _ )
-- -- -- -- -- -- --     where module D = GroupoidObjectsCategory D
-- -- -- -- -- -- --   CAT .⋆ᴴIdL {y = D} {f = F} α =
-- -- -- -- -- -- --     makeNatTransPathP _ _ (funExt λ _ → cong₂ D._⋆_ (F .F-id) refl ∙ D.⋆IdL _)
-- -- -- -- -- -- --     where module D = GroupoidObjectsCategory D
-- -- -- -- -- -- --   CAT .⋆ᴴIdR {y = D} α =
-- -- -- -- -- -- --     makeNatTransPathP _ _ (funExt λ _ → D.⋆IdR _)
-- -- -- -- -- -- --     where module D = GroupoidObjectsCategory D
-- -- -- -- -- -- --   CAT .⋆ᴴAssoc {w = D} {f = F} {g = G} {h = H} _ _ _ =
-- -- -- -- -- -- --     makeNatTransPathP _ _
-- -- -- -- -- -- --       (funExt λ _ →
-- -- -- -- -- -- --         D.⟨ H .F-seq _ _ ⟩⋆⟨ refl ⟩
-- -- -- -- -- -- --         ∙ D.⋆Assoc _ _ _
-- -- -- -- -- -- --       )
-- -- -- -- -- -- --     where module D = GroupoidObjectsCategory D
-- -- -- -- -- -- --   CAT .interchange {z = D}{k = k} α β γ δ =
-- -- -- -- -- -- --     makeNatTransPath (funExt λ _ →
-- -- -- -- -- -- --       (sym $ D.⋆Assoc _ _ _)
-- -- -- -- -- -- --       ∙ D.⟨ D.⟨ k .F-seq _ _ ⟩⋆⟨ refl ⟩
-- -- -- -- -- -- --                 ∙ D.⋆Assoc _ _ _
-- -- -- -- -- -- --                 ∙ D.⟨ refl ⟩⋆⟨ N-hom γ (N-ob β _) ⟩
-- -- -- -- -- -- --                 ∙ (sym $ D.⋆Assoc _ _ _)
-- -- -- -- -- -- --           ⟩⋆⟨ refl ⟩
-- -- -- -- -- -- --       ∙ D.⋆Assoc _ _ _)
-- -- -- -- -- -- --     where module D = GroupoidObjectsCategory D
-- -- -- -- -- -- --   CAT .isGroupoidHom₁ {y = D} = isOfHLevelFunctor 1 D.groupoid-obs
-- -- -- -- -- -- --     where module D = GroupoidObjectsCategory D
-- -- -- -- -- -- --   CAT .isSetHom₂ = isSetNatTrans

-- -- -- -- -- -- -- module _ {ℓC ℓC'} (C : Category ℓC ℓC') where
-- -- -- -- -- -- --   private
-- -- -- -- -- -- --     module C = Category C

-- -- -- -- -- -- --   Cat→2Cat : 2Category _ _ _
-- -- -- -- -- -- --   Cat→2Cat .ob = C.ob
-- -- -- -- -- -- --   Cat→2Cat .Hom₁[_,_] = C.Hom[_,_]
-- -- -- -- -- -- --   Cat→2Cat .Hom₂[_,_] f g = f ≡ g
-- -- -- -- -- -- --   Cat→2Cat .id₁ = C.id
-- -- -- -- -- -- --   Cat→2Cat .id₂ = refl
-- -- -- -- -- -- --   Cat→2Cat ._⋆₁_ = C._⋆_
-- -- -- -- -- -- --   Cat→2Cat ._⋆ⱽ_ = _∙_
-- -- -- -- -- -- --   Cat→2Cat ._⋆ᴴ_ = C.⟨_⟩⋆⟨_⟩
-- -- -- -- -- -- --   Cat→2Cat .⋆₁IdL = C.⋆IdL
-- -- -- -- -- -- --   Cat→2Cat .⋆₁IdR = C.⋆IdR
-- -- -- -- -- -- --   Cat→2Cat .⋆₁Assoc = C.⋆Assoc
-- -- -- -- -- -- --   Cat→2Cat .⋆ⱽIdL _ = C.isSetHom _ _ _ _
-- -- -- -- -- -- --   Cat→2Cat .⋆ⱽIdR _ = C.isSetHom _ _ _ _
-- -- -- -- -- -- --   Cat→2Cat .⋆ⱽAssoc _ _ _ = C.isSetHom _ _ _ _
-- -- -- -- -- -- --   Cat→2Cat .⋆ᴴIdL _ = isProp→PathP (λ _ → C.isSetHom _ _) _ _
-- -- -- -- -- -- --   Cat→2Cat .⋆ᴴIdR _ = isProp→PathP (λ _ → C.isSetHom _ _) _ _
-- -- -- -- -- -- --   Cat→2Cat .⋆ᴴAssoc _ _ _ = isProp→PathP (λ _ → C.isSetHom _ _) _ _
-- -- -- -- -- -- --   Cat→2Cat .interchange  _ _ _ _ = C.isSetHom _ _ _ _
-- -- -- -- -- -- --   Cat→2Cat .isGroupoidHom₁ = isSet→isGroupoid C.isSetHom
-- -- -- -- -- -- --   Cat→2Cat .isSetHom₂ = isSet→isGroupoid C.isSetHom _ _

-- -- -- -- -- -- -- --   Cat→2CatEq : 2Category _ _ _
-- -- -- -- -- -- -- --   Cat→2CatEq .ob = C.ob
-- -- -- -- -- -- -- --   Cat→2CatEq .Hom₁[_,_] = C.Hom[_,_]
-- -- -- -- -- -- -- --   Cat→2CatEq .Hom₂[_,_] f g = f Eq.≡ g
-- -- -- -- -- -- -- --   Cat→2CatEq .id₁ = C.id
-- -- -- -- -- -- -- --   Cat→2CatEq .id₂ = Eq.refl
-- -- -- -- -- -- -- --   Cat→2CatEq ._⋆₁_ = C._⋆_
-- -- -- -- -- -- -- --   Cat→2CatEq ._⋆ⱽ_ = Eq._∙_
-- -- -- -- -- -- -- --   Cat→2CatEq ._⋆ᴴ_ Eq.refl Eq.refl = Eq.refl
-- -- -- -- -- -- -- --   Cat→2CatEq .⋆₁IdL = C.⋆IdL
-- -- -- -- -- -- -- --   Cat→2CatEq .⋆₁IdR = C.⋆IdR
-- -- -- -- -- -- -- --   Cat→2CatEq .⋆₁Assoc = C.⋆Assoc
-- -- -- -- -- -- -- --   Cat→2CatEq .⋆ⱽIdL _ = refl
-- -- -- -- -- -- -- --   Cat→2CatEq .⋆ⱽIdR Eq.refl = refl
-- -- -- -- -- -- -- --   Cat→2CatEq .⋆ⱽAssoc Eq.refl Eq.refl Eq.refl = refl
-- -- -- -- -- -- -- --   Cat→2CatEq .interchange Eq.refl Eq.refl Eq.refl Eq.refl = refl
-- -- -- -- -- -- -- --   Cat→2CatEq .isGroupoidHom₁ = isSet→isGroupoid C.isSetHom
-- -- -- -- -- -- -- --   Cat→2CatEq .isSetHom₂ = isSetRetract Eq.eqToPath Eq.pathToEq
-- -- -- -- -- -- -- --     Eq.pathToEq-eqToPath (isSet→isGroupoid C.isSetHom _ _)

-- -- -- -- -- -- -- module _ {ℓC ℓC' ℓC''} (C : 2Category ℓC ℓC' ℓC'') where
-- -- -- -- -- -- --   private
-- -- -- -- -- -- --     module C = 2Category C
-- -- -- -- -- -- --   _^op2 : 2Category ℓC ℓC' ℓC''
-- -- -- -- -- -- --   _^op2 .ob = C.ob
-- -- -- -- -- -- --   _^op2 .Hom₁[_,_] x y = C.Hom₁[ y , x ]
-- -- -- -- -- -- --   _^op2 .Hom₂[_,_] f g = C.Hom₂[ g , f ]
-- -- -- -- -- -- --   _^op2 .id₁ = C.id₁
-- -- -- -- -- -- --   _^op2 .id₂ = C.id₂
-- -- -- -- -- -- --   _^op2 ._⋆₁_ = λ f g → g C.⋆₁ f
-- -- -- -- -- -- --   _^op2 ._⋆ⱽ_ = λ z z₁ → z₁ C.⋆ⱽ z
-- -- -- -- -- -- --   _^op2 ._⋆ᴴ_ = λ z₁ z₂ → z₂ C.⋆ᴴ z₁
-- -- -- -- -- -- --   _^op2 .⋆₁IdL = C.⋆₁IdR
-- -- -- -- -- -- --   _^op2 .⋆₁IdR = C.⋆₁IdL
-- -- -- -- -- -- --   _^op2 .⋆₁Assoc _ _ _ = sym $ C.⋆₁Assoc _ _ _
-- -- -- -- -- -- --   _^op2 .⋆ⱽIdL = C.⋆ⱽIdR
-- -- -- -- -- -- --   _^op2 .⋆ⱽIdR = C.⋆ⱽIdL
-- -- -- -- -- -- --   _^op2 .⋆ⱽAssoc _ _ _ = sym $ C.⋆ⱽAssoc _ _ _
-- -- -- -- -- -- --   _^op2 .⋆ᴴIdL = C.⋆ᴴIdR
-- -- -- -- -- -- --   _^op2 .⋆ᴴIdR = C.⋆ᴴIdL
-- -- -- -- -- -- --   _^op2 .⋆ᴴAssoc _ _ _ = symP $ C.⋆ᴴAssoc _ _ _
-- -- -- -- -- -- --   _^op2 .interchange = λ α β γ δ → C.interchange δ γ β α
-- -- -- -- -- -- --   _^op2 .isGroupoidHom₁ = C.isGroupoidHom₁
-- -- -- -- -- -- --   _^op2 .isSetHom₂ = C.isSetHom₂
