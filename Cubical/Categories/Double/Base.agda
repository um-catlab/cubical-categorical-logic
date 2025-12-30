module Cubical.Categories.Double.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

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
    -- isSetHomⱽ : ∀ {x y} → isSet Homⱽ[ x , y ]

    -- Weak horizontal morphisms
    Homᴴ[_,_] : (x y : ob) → Type ℓH
    idᴴ   : ∀ {x} → Homᴴ[ x , x ]
    _⋆ᴴ_  : ∀ {x y z} →
      (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) → Homᴴ[ x , z ]
    -- isSetHomᴴ : ∀ {x y} → isSet Homᴴ[ x , y ]

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

open DoubleCategory

module _ {ℓC ℓC'}
  (C : Category ℓC ℓC') (pb : Pullbacks C)
  where
  private
    module C = Category C


  record Span (l r : C.ob) : Type (ℓ-max ℓC ℓC') where
    constructor span
    field
      apex : C.ob
      s₁ : C.Hom[ apex , l ]
      s₂ : C.Hom[ apex , r ]

  open Span

  record SpanMor {x y z w} (S : Span x y) (T : Span z w)
                   (f : C.Hom[ x , z ]) (g : C.Hom[ y , w ]) :
         Type ℓC' where
      constructor spanmor
      private
        module S = Span S
        module T = Span T
      field
        apexMor : C.Hom[ S.apex , T.apex ]
        commL   : S.s₁ C.⋆ f ≡ apexMor C.⋆ T.s₁
        commR   : S.s₂ C.⋆ g ≡ apexMor C.⋆ T.s₂

  SpanMorΣ :
    ∀ {x y z w} (S : Span x y) → (T : Span z w) →
    (f : C.Hom[ x , z ]) → (g : C.Hom[ y , w ]) → Type ℓC'
  SpanMorΣ S T f g =
    Σ[ apexMor ∈ C.Hom[ apex S , apex T ] ]
    Σ[ commL ∈ S .s₁ C.⋆ f ≡ apexMor C.⋆ T .s₁ ]
      (S .s₂ C.⋆ g ≡ apexMor C.⋆ T .s₂)

  isSetSpanMorΣ :
    ∀ {x y z w} (S : Span x y) → (T : Span z w) →
    (f : C.Hom[ x , z ]) → (g : C.Hom[ y , w ]) → isSet (SpanMorΣ S T f g)
  isSetSpanMorΣ S T f g =
    isSetΣ C.isSetHom
      (λ _ → isSetΣ (isProp→isSet (C.isSetHom _ _))
      (λ _ → isProp→isSet (C.isSetHom _ _)))

  module _
    {x y z w} (S : Span x y) (T : Span z w)
    (f : C.Hom[ x , z ]) (g : C.Hom[ y , w ])
    where
    SpanMorIso : Iso (SpanMor S T f g) (SpanMorΣ S T f g)
    unquoteDef SpanMorIso = defineRecordIsoΣ SpanMorIso (quote (SpanMor))

  isSetSpanMor :
    ∀ {x y z w} (S : Span x y) → (T : Span z w) →
    (f : C.Hom[ x , z ]) → (g : C.Hom[ y , w ]) → isSet (SpanMor S T f g)
  isSetSpanMor S T f g =
    isOfHLevelRetractFromIso 2 (SpanMorIso S T f g) (isSetSpanMorΣ S T f g)

  idSpan : ∀ {c} → Span c c
  idSpan = span _ C.id C.id

  open Pullback

  seqSpan : ∀ {x y z} → Span x y → Span y z → Span x z
  seqSpan {x = x} {y = y} {z = z} r s =
    span (pb (cospan (r .apex) y (s .apex) (r .s₂) (s .s₁)) .pbOb)
      (pb (cospan (r .apex) y (s .apex) (r .s₂) (s .s₁)) .pbPr₁ C.⋆ r .s₁)
      (pb (cospan (r .apex) y (s .apex) (r .s₂) (s .s₁)) .pbPr₂ C.⋆ s .s₂)

  open SpanMor
  -- TODO
  -- Category should have Assoc⁻ so Agsy search is better
  module _ {A A' B B' : C.ob} where

    -- PathP over varying spans and boundary morphisms
    SpanMorPathP :
      {S₀ S₁ : Span A B} {T₀ T₁ : Span A' B'}
      {f₀ f₁ : C.Hom[ A , A' ]} {g₀ g₁ : C.Hom[ B , B' ]}
      {α : SpanMor S₀ T₀ f₀ g₀} {β : SpanMor S₁ T₁ f₁ g₁}
      (pS : S₀ ≡ S₁) (pT : T₀ ≡ T₁) (pf : f₀ ≡ f₁) (pg : g₀ ≡ g₁) →
      PathP (λ i → C.Hom[ Span.apex (pS i) , Span.apex (pT i) ])
            (SpanMor.apexMor α) (SpanMor.apexMor β) →
      PathP (λ i → SpanMor (pS i) (pT i) (pf i) (pg i)) α β
    SpanMorPathP {S₀} {S₁} {T₀} {T₁} {f₀} {f₁} {g₀} {g₁} {α} {β} pS pT pf pg pApex i =
      spanmor
        (pApex i)
        (isProp→PathP
          (λ i → C.isSetHom
            (Span.s₁ (pS i) C.⋆ pf i)
            (pApex i C.⋆ Span.s₁ (pT i)))
          (SpanMor.commL α)
          (SpanMor.commL β) i)
        (isProp→PathP
          (λ i → C.isSetHom
            (Span.s₂ (pS i) C.⋆ pg i)
            (pApex i C.⋆ Span.s₂ (pT i)))
          (SpanMor.commR α)
          (SpanMor.commR β) i)

  module _ {A A' B B' : C.ob} {S : Span A B} {T : Span A' B'}
           {f : C.Hom[ A , A' ]} {g : C.Hom[ B , B' ]} where

    private
      module S = Span S
      module T = Span T

    -- Full path characterization
    SpanMorPath : {α β : SpanMor S T f g} →
      SpanMor.apexMor α ≡ SpanMor.apexMor β →
      α ≡ β
    SpanMorPath {α} {β} p i = spanmor
      (p i)
      (isProp→PathP (λ i → C.isSetHom (S.s₁ C.⋆ f) (p i C.⋆ T.s₁))
                    (SpanMor.commL α) (SpanMor.commL β) i)
      (isProp→PathP (λ i → C.isSetHom (S.s₂ C.⋆ g) (p i C.⋆ T.s₂))
                    (SpanMor.commR α) (SpanMor.commR β) i)

  SPAN : DoubleCategory _ _ _ _
  SPAN .ob = C.ob
  SPAN .Homⱽ[_,_] = C.Hom[_,_]
  SPAN .idⱽ = C.id
  SPAN ._⋆ⱽ_ = C._⋆_
  SPAN .⋆ⱽIdL = C.⋆IdL
  SPAN .⋆ⱽIdR = C.⋆IdR
  SPAN .⋆ⱽAssoc = C.⋆Assoc
  -- SPAN .isSetHomⱽ = C.isSetHom
  SPAN .Homᴴ[_,_] = Span
  SPAN .idᴴ = idSpan
  SPAN ._⋆ᴴ_ = seqSpan
  -- SPAN .isSetHomᴴ = {!!}
  SPAN .Sq = SpanMor
  SPAN .idⱽSq =
    spanmor C.id (C.⋆IdR _ ∙ (sym $ C.⋆IdL _)) (C.⋆IdR _ ∙ (sym $ C.⋆IdL _))
  SPAN .idᴴSq {v = f} =
    spanmor f (C.⋆IdL _ ∙ (sym $ C.⋆IdR _)) (C.⋆IdL _ ∙ (sym $ C.⋆IdR _))
  SPAN ._⋆ⱽSq_ {←f' = ←f'} ϕ ψ =
    spanmor (ϕ .apexMor C.⋆ ψ .apexMor)
      ((sym $ C.⋆Assoc _ _ _)
      ∙ cong (C._⋆ ←f') (ϕ .commL)
      ∙ C.⋆Assoc _ _ _
      ∙ cong₂ C._⋆_ refl (ψ .commL)
      ∙ (sym $ C.⋆Assoc _ _ _))
      ((sym $ C.⋆Assoc _ _ _)
      ∙ cong₂ C._⋆_ (ϕ .commR) refl
      ∙ C.⋆Assoc _ _ _
      ∙ cong₂ C._⋆_ refl (ψ .commR)
      ∙ (sym $ C.⋆Assoc _ _ _))
  SPAN .⋆ⱽIdLSq _ = SpanMorPathP _ _ _ _ (C.⋆IdL _)
  SPAN .⋆ⱽIdRSq _ = SpanMorPathP _ _ _ _ (C.⋆IdR _)
  SPAN .⋆ⱽAssocSq _ _ _ = SpanMorPathP _ _ _ _ (C.⋆Assoc _ _ _)
  SPAN ._⋆ᴴSq_ α β = {!!}
  SPAN .λᴴ s =
    spanmor
      (pb (cospan (apex (SPAN .idᴴ)) _ (apex s) (s₂ (SPAN .idᴴ)) (s₁ s)) .pbPr₂)
      (C.⋆IdR _ ∙ pb (cospan (apex (SPAN .idᴴ)) _ (apex s) (s₂ (SPAN .idᴴ)) (s₁ s))
                   .pbCommutes)
      (C.⋆IdR _ ∙ refl)
  SPAN .λᴴ⁻ s = {!!}
  SPAN .λᴴλᴴ⁻ = {!!}
  SPAN .λᴴ⁻λᴴ = {!!}
  SPAN .λᴴ-nat = {!!}
  SPAN .ρᴴ = {!!}
  SPAN .ρᴴ⁻ = {!!}
  SPAN .ρᴴρᴴ⁻ = {!!}
  SPAN .ρᴴ⁻ρᴴ = {!!}
  SPAN .ρᴴ-nat = {!!}
  SPAN .αᴴ = {!!}
  SPAN .αᴴ⁻ = {!!}
  SPAN .αᴴαᴴ⁻ = {!!}
  SPAN .αᴴ⁻αᴴ = {!!}
  SPAN .αᴴ-nat = {!!}
  SPAN .pentagon = {!!}
  SPAN .triangle = {!!}
  SPAN .interchange = {!!}
