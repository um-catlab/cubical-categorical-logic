{-# OPTIONS --lossy-unification #-}
{-

  FORDED DISPLAYED CATEGORIES.

  The displayed counterpart of Cubical.Categories.Functors.Strict.Base.
  There, a functor's laws are forded --- instead of `F ⟪ id ⟫ ≡ id` the
  field takes ANY `f` together with a witness `id ≡ f` --- and the
  payoff is that `_S∘_` is definitionally unital and associative for
  VARIABLE functors, because composition passes the ford along instead
  of building a `_∙_` chain.

  Doing the same to `Categoryᴰ` buys three things that the stock
  definition does not have.

  1. REINDEXING IS TRANSPORT-FREE.  `reindexS` below contains no
     `subst`, `transport` or `reind`: each field hands the functor's
     own ford to the displayed category's ford.  Contrast
     Displayed.Instances.Reindex.Base, whose `idᴰ` is
     `R.reind (sym F-id) idᴰ`.

  2. REINDEXING IS STRICTLY FUNCTORIAL.  `reindexS SId ≡ id` and
     `reindexS (G S∘ F) ≡ reindexS F ∘ reindexS G`, both by `refl`, both
     for variables.  The stock `reindex Cᴰ Id ≡ Cᴰ` fails --- twice
     over, since `Categoryᴰ` is also declared `no-eta-equality`.

  3. THE LAWS ARE HOMOGENEOUS.  Because the composite's base hom is a
     parameter, it can be pinned to the one the other side already
     lives over, so ⋆IdLᴰ/⋆IdRᴰ/⋆Assocᴰ are ordinary equations rather
     than PathPs.  Same phenomenon as Multicategory.Shaped: nothing is
     built, so nothing has to transport along.

  `Ext` at the bottom is the difference-list presentation of a context
  former: a uniform operation on the slice over C, rather than an
  object of it.  Its concatenation is definitionally unital and
  associative in any association, which is what makes iterated context
  formation order-independent, and `⌜_⌝` shows every forded displayed
  category is one --- recovering `∫ᶠ` and its display map on the nose.

  TODO: `Ext` pins every category to a single level pair.  Real
  telescopes raise levels, so this wants the level-indexed treatment of
  Cubical.Categories.LocallySmall.

-}
module Cubical.Categories.Displayed.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functors.Strict.Base
open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Displayed.Reasoning as Reasoning

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓᴰ ℓᴰ' : Level

open StrictFunctor

record Categoryᶠᴰ (C : Category ℓC ℓC') (ℓᴰ ℓᴰ' : Level)
  : Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓᴰ ℓᴰ'))) where
  -- eta-equality is the DEFAULT and is load-bearing: it is what makes
  -- two records with definitionally equal fields definitionally equal.
  -- Do not add no-eta-equality.
  private module C = Category C
  field
    ob[_] : C.ob → Type ℓᴰ
    Hom[_][_,_] : {x y : C.ob} → C [ x , y ] → ob[ x ] → ob[ y ] → Type ℓᴰ'

    idᴰ : {x : C.ob} {xᴰ : ob[ x ]}
      (i : C [ x , x ]) → C.id Eq.≡ i → Hom[ i ][ xᴰ , xᴰ ]

    ⋆ᴰ : {x y z : C.ob} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
      (f : C [ x , y ]) (g : C [ y , z ]) (h : C [ x , z ])
      → f C.⋆ g Eq.≡ h
      → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ h ][ xᴰ , zᴰ ]

    -- THE LAWS, homogeneous: not a PathP in sight.
    ⋆IdLᴰ : {x y : C.ob} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
      (i : C [ x , x ]) (ei : C.id Eq.≡ i)
      (f : C [ x , y ]) (e : i C.⋆ f Eq.≡ f)
      (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
      → ⋆ᴰ i f f e (idᴰ i ei) fᴰ ≡ fᴰ

    ⋆IdRᴰ : {x y : C.ob} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
      (f : C [ x , y ]) (i : C [ y , y ]) (ei : C.id Eq.≡ i)
      (e : f C.⋆ i Eq.≡ f)
      (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
      → ⋆ᴰ f i f e fᴰ (idᴰ i ei) ≡ fᴰ

    ⋆Assocᴰ : {w x y z : C.ob}
      {wᴰ : ob[ w ]} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
      (f : C [ w , x ]) (g : C [ x , y ]) (h : C [ y , z ])
      (fg : C [ w , y ]) (efg : f C.⋆ g Eq.≡ fg)
      (gh : C [ x , z ]) (egh : g C.⋆ h Eq.≡ gh)
      (k : C [ w , z ]) (e₁ : fg C.⋆ h Eq.≡ k) (e₂ : f C.⋆ gh Eq.≡ k)
      (fᴰ : Hom[ f ][ wᴰ , xᴰ ]) (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
      (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
      → ⋆ᴰ fg h k e₁ (⋆ᴰ f g fg efg fᴰ gᴰ) hᴰ
        ≡ ⋆ᴰ f gh k e₂ fᴰ (⋆ᴰ g h gh egh gᴰ hᴰ)

    -- FORD COHERENCES: the ford is bookkeeping only, the displayed data
    -- depends on the base hom and not on which witness produced it.
    -- These are what let ∫ᶠ below be built, since there the composite
    -- lands over `f ⋆ g` with witness refl rather than over a pinned
    -- target.
    idᴰ-coh : {x : C.ob} {xᴰ : ob[ x ]}
      (i i' : C [ x , x ]) (ei : C.id Eq.≡ i) (ei' : C.id Eq.≡ i')
      (p : i ≡ i')
      → PathP (λ k → Hom[ p k ][ xᴰ , xᴰ ]) (idᴰ i ei) (idᴰ i' ei')

    ⋆ᴰ-coh : {x y z : C.ob} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
      (f : C [ x , y ]) (g : C [ y , z ]) (h h' : C [ x , z ])
      (e : f C.⋆ g Eq.≡ h) (e' : f C.⋆ g Eq.≡ h') (p : h ≡ h')
      (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Hom[ g ][ yᴰ , zᴰ ])
      → PathP (λ k → Hom[ p k ][ xᴰ , zᴰ ])
          (⋆ᴰ f g h e fᴰ gᴰ) (⋆ᴰ f g h' e' fᴰ gᴰ)

    isSetHomᴰ : {x y : C.ob} {f : C [ x , y ]}
      {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} → isSet Hom[ f ][ xᴰ , yᴰ ]

open Categoryᶠᴰ

-- ------------------------------------------------------------------
-- REINDEXING along a strict functor.  No subst, no transport, no
-- reind: the functor's ford goes straight into the displayed one.
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : StrictFunctor C D) (Dᴰ : Categoryᶠᴰ D ℓᴰ ℓᴰ') where

  reindexS : Categoryᶠᴰ C ℓᴰ ℓᴰ'
  reindexS .ob[_] c = Dᴰ .ob[_] (F .F-ob c)
  reindexS .Hom[_][_,_] f aᴰ bᴰ = Dᴰ .Hom[_][_,_] (F .F-hom f) aᴰ bᴰ
  reindexS .idᴰ i ei = Dᴰ .idᴰ (F .F-hom i) (F .F-id i ei)
  reindexS .⋆ᴰ f g h e fᴰ gᴰ =
    Dᴰ .⋆ᴰ (F .F-hom f) (F .F-hom g) (F .F-hom h)
      (F .F-seq f g h e) fᴰ gᴰ
  reindexS .⋆IdLᴰ i ei f e fᴰ =
    Dᴰ .⋆IdLᴰ (F .F-hom i) (F .F-id i ei)
      (F .F-hom f) (F .F-seq i f f e) fᴰ
  reindexS .⋆IdRᴰ f i ei e fᴰ =
    Dᴰ .⋆IdRᴰ (F .F-hom f) (F .F-hom i) (F .F-id i ei)
      (F .F-seq f i f e) fᴰ
  reindexS .⋆Assocᴰ f g h fg efg gh egh k e₁ e₂ fᴰ gᴰ hᴰ =
    Dᴰ .⋆Assocᴰ (F .F-hom f) (F .F-hom g) (F .F-hom h)
      (F .F-hom fg) (F .F-seq f g fg efg)
      (F .F-hom gh) (F .F-seq g h gh egh)
      (F .F-hom k) (F .F-seq fg h k e₁) (F .F-seq f gh k e₂)
      fᴰ gᴰ hᴰ
  reindexS .idᴰ-coh i i' ei ei' p =
    Dᴰ .idᴰ-coh (F .F-hom i) (F .F-hom i')
      (F .F-id i ei) (F .F-id i' ei') (cong (F .F-hom) p)
  reindexS .⋆ᴰ-coh f g h h' e e' p fᴰ gᴰ =
    Dᴰ .⋆ᴰ-coh (F .F-hom f) (F .F-hom g) (F .F-hom h) (F .F-hom h')
      (F .F-seq f g h e) (F .F-seq f g h' e')
      (cong (F .F-hom) p) fᴰ gᴰ
  reindexS .isSetHomᴰ = Dᴰ .isSetHomᴰ

-- reindexing is STRICTLY functorial, for variables.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ') where
  reindexS-Id : reindexS SId Cᴰ ≡ Cᴰ
  reindexS-Id = refl

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  (F : StrictFunctor C D) (G : StrictFunctor D E) (Eᴰ : Categoryᶠᴰ E ℓᴰ ℓᴰ')
  where
  reindexS-comp : reindexS (G S∘ F) Eᴰ ≡ reindexS F (reindexS G Eᴰ)
  reindexS-comp = refl

-- ------------------------------------------------------------------
-- THE TOTAL CATEGORY, and its display map as a STRICT functor.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ') where
  private
    module C = Category C
    module Cᴰ = Categoryᶠᴰ Cᴰ
  open Category

  ∫ᶠ : Category (ℓ-max ℓC ℓᴰ) (ℓ-max ℓC' ℓᴰ')
  ∫ᶠ .ob = Σ[ x ∈ C.ob ] Cᴰ.ob[ x ]
  ∫ᶠ .Hom[_,_] (x , xᴰ) (y , yᴰ) = Σ[ f ∈ C [ x , y ] ] Cᴰ.Hom[ f ][ xᴰ , yᴰ ]
  ∫ᶠ .id = C.id , Cᴰ.idᴰ C.id Eq.refl
  ∫ᶠ ._⋆_ (f , fᴰ) (g , gᴰ) = (f C.⋆ g) , Cᴰ.⋆ᴰ f g (f C.⋆ g) Eq.refl fᴰ gᴰ
  ∫ᶠ .⋆IdL (f , fᴰ) = ΣPathP (C.⋆IdL f ,
    (Cᴰ.⋆ᴰ-coh C.id f (C.id C.⋆ f) f Eq.refl (Eq.pathToEq (C.⋆IdL f))
       (C.⋆IdL f) (Cᴰ.idᴰ C.id Eq.refl) fᴰ)
    ▷ Cᴰ.⋆IdLᴰ C.id Eq.refl f (Eq.pathToEq (C.⋆IdL f)) fᴰ)
  ∫ᶠ .⋆IdR (f , fᴰ) = ΣPathP (C.⋆IdR f ,
    (Cᴰ.⋆ᴰ-coh f C.id (f C.⋆ C.id) f Eq.refl (Eq.pathToEq (C.⋆IdR f))
       (C.⋆IdR f) fᴰ (Cᴰ.idᴰ C.id Eq.refl))
    ▷ Cᴰ.⋆IdRᴰ f C.id Eq.refl (Eq.pathToEq (C.⋆IdR f)) fᴰ)
  ∫ᶠ .⋆Assoc (f , fᴰ) (g , gᴰ) (h , hᴰ) = ΣPathP (C.⋆Assoc f g h ,
    Cᴰ.⋆Assocᴰ f g h (f C.⋆ g) Eq.refl (g C.⋆ h) Eq.refl
      ((f C.⋆ g) C.⋆ h) Eq.refl (Eq.pathToEq (sym (C.⋆Assoc f g h)))
      fᴰ gᴰ hᴰ
    ◁ Cᴰ.⋆ᴰ-coh f (g C.⋆ h) ((f C.⋆ g) C.⋆ h) (f C.⋆ (g C.⋆ h))
        (Eq.pathToEq (sym (C.⋆Assoc f g h))) Eq.refl (C.⋆Assoc f g h)
        fᴰ (Cᴰ.⋆ᴰ g h (g C.⋆ h) Eq.refl gᴰ hᴰ))
  ∫ᶠ .isSetHom = isSetΣ C.isSetHom (λ _ → Cᴰ.isSetHomᴰ)

  -- both laws are just `cong fst`; nothing is built, so nothing bends
  Fstᶠ : StrictFunctor ∫ᶠ C
  Fstᶠ .F-ob = fst
  Fstᶠ .F-hom = fst
  Fstᶠ .F-id f e = Eq.ap fst e
  Fstᶠ .F-seq f g h e = Eq.ap fst e

-- ------------------------------------------------------------------
-- THE DIFFERENCE-LIST PRESENTATION of a context former: a uniform
-- operation on the slice over C, not an object of it.  Concatenation
-- never pulls anything back --- it asks the second former to build
-- itself over the first's output --- which is why it is composition of
-- functions, hence definitionally associative.
record Ext (C : Category ℓC ℓC') : Type (ℓ-suc (ℓ-max ℓC ℓC')) where
  field
    at   : (E : Category ℓC ℓC') → StrictFunctor E C → Category ℓC ℓC'
    disp : (E : Category ℓC ℓC') (p : StrictFunctor E C)
         → StrictFunctor (at E p) E

open Ext

module _ {C : Category ℓC ℓC'} where
  εE : Ext C
  εE .at   E p = E
  εE .disp E p = SId

  _·_ : Ext C → Ext C → Ext C
  (Δ · Θ) .at E p = Θ .at (Δ .at E p) (p S∘ Δ .disp E p)
  (Δ · Θ) .disp E p =
    Δ .disp E p S∘ Θ .disp (Δ .at E p) (p S∘ Δ .disp E p)

  ext-lUnit : (Δ : Ext C) → (εE · Δ) ≡ Δ
  ext-lUnit Δ = refl

  ext-rUnit : (Δ : Ext C) → (Δ · εE) ≡ Δ
  ext-rUnit Δ = refl

  ext-assoc : (Δ Θ Ξ : Ext C) → ((Δ · Θ) · Ξ) ≡ (Δ · (Θ · Ξ))
  ext-assoc Δ Θ Ξ = refl

  -- THE BRIDGE, general form.  A context former is a family of
  -- displayed categories UNIFORM in the base built so far --- which is
  -- how a DEPENDENT telescope step is written here: the family may use
  -- `p` to reindex.  A single `Categoryᶠᴰ (∫ᶠ Cᴰ)` is not an `Ext C`,
  -- because there is no map into `∫ᶠ Cᴰ` from an arbitrary `E`.
  ⌜_⌝ᵘ : ((E : Category ℓC ℓC') → StrictFunctor E C → Categoryᶠᴰ E ℓC ℓC')
       → Ext C
  ⌜ Φ ⌝ᵘ .at   E p = ∫ᶠ (Φ E p)
  ⌜ Φ ⌝ᵘ .disp E p = Fstᶠ (Φ E p)

  -- the non-dependent former is the special case that reindexes a
  -- single displayed category along whatever display map it is given.
  ⌜_⌝ : Categoryᶠᴰ C ℓC ℓC' → Ext C
  ⌜ Cᴰ ⌝ .at   E p = ∫ᶠ (reindexS p Cᴰ)
  ⌜ Cᴰ ⌝ .disp E p = Fstᶠ (reindexS p Cᴰ)

  ⌜⌝-is-⌜⌝ᵘ : (Cᴰ : Categoryᶠᴰ C ℓC ℓC')
    → ⌜ Cᴰ ⌝ ≡ ⌜ (λ E p → reindexS p Cᴰ) ⌝ᵘ
  ⌜⌝-is-⌜⌝ᵘ Cᴰ = refl

  -- and it recovers the total category and its display map ON THE NOSE,
  -- which is exactly what the stock `reindex` cannot do.
  bridge-∫ : (Cᴰ : Categoryᶠᴰ C ℓC ℓC') → ⌜ Cᴰ ⌝ .at C SId ≡ ∫ᶠ Cᴰ
  bridge-∫ Cᴰ = refl

  bridge-disp : (Cᴰ : Categoryᶠᴰ C ℓC ℓC') → ⌜ Cᴰ ⌝ .disp C SId ≡ Fstᶠ Cᴰ
  bridge-disp Cᴰ = refl

-- reindexing a former is substituting its display map, definitionally
module _ {C : Category ℓC ℓC'} {D : Category ℓC ℓC'}
  (F : StrictFunctor D C) (Cᴰ : Categoryᶠᴰ C ℓC ℓC') where

  bridge-reindex : (E : Category ℓC ℓC') (p : StrictFunctor E D)
    → ⌜ reindexS F Cᴰ ⌝ .at E p ≡ ⌜ Cᴰ ⌝ .at E (F S∘ p)
  bridge-reindex E p = refl

-- ------------------------------------------------------------------
-- ITERATED CONTEXT FORMATION IS ORDER-INDEPENDENT.  A three-step
-- telescope built in either association is definitionally the same
-- former, gives the definitionally same total category, and the
-- definitionally same composite display map.
module _ {C : Category ℓC ℓC'}
  (Aᴰ Bᴰ Cᴰ : Categoryᶠᴰ C ℓC ℓC') where

  tele-assoc : ((⌜ Aᴰ ⌝ · ⌜ Bᴰ ⌝) · ⌜ Cᴰ ⌝) ≡ (⌜ Aᴰ ⌝ · (⌜ Bᴰ ⌝ · ⌜ Cᴰ ⌝))
  tele-assoc = refl

  tele-at : ((⌜ Aᴰ ⌝ · ⌜ Bᴰ ⌝) · ⌜ Cᴰ ⌝) .at C SId
          ≡ (⌜ Aᴰ ⌝ · (⌜ Bᴰ ⌝ · ⌜ Cᴰ ⌝)) .at C SId
  tele-at = refl

  tele-disp : ((⌜ Aᴰ ⌝ · ⌜ Bᴰ ⌝) · ⌜ Cᴰ ⌝) .disp C SId
            ≡ (⌜ Aᴰ ⌝ · (⌜ Bᴰ ⌝ · ⌜ Cᴰ ⌝)) .disp C SId
  tele-disp = refl

  tele-unitL : (εE · (⌜ Aᴰ ⌝ · ⌜ Bᴰ ⌝)) ≡ (⌜ Aᴰ ⌝ · ⌜ Bᴰ ⌝)
  tele-unitL = refl

  tele-unitMid : ((⌜ Aᴰ ⌝ · εE) · ⌜ Bᴰ ⌝) ≡ (⌜ Aᴰ ⌝ · ⌜ Bᴰ ⌝)
  tele-unitMid = refl

  tele-unitR : ((⌜ Aᴰ ⌝ · ⌜ Bᴰ ⌝) · εE) ≡ (⌜ Aᴰ ⌝ · ⌜ Bᴰ ⌝)
  tele-unitR = refl

-- ------------------------------------------------------------------
-- EVERY displayed category is a forded one.  This is what makes the
-- above more than a definition: the whole existing library of
-- Categoryᴰ instances plugs in, and the two ford coherences are
-- discharged generically by `rectify`, since a ford is a path in a
-- hom-SET and any two agree.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ') where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module R = Reasoning Cᴰ

    -- An Eq-valued reind.  Unlike `R.reind`, `Eq.transport _ Eq.refl b`
    -- REDUCES to `b`, so the lifted idᴰ/⋆ᴰ compute wherever the ford is
    -- refl -- which is everywhere ∫ᶠ uses them.
    reindE : {x y : Category.ob C} {f g : C [ x , y ]}
      {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      → f Eq.≡ g → Cᴰ.Hom[ f ][ xᴰ , yᴰ ] → Cᴰ.Hom[ g ][ xᴰ , yᴰ ]
    reindE p fᴰ = Eq.transport (λ h → Cᴰ.Hom[ h ][ _ , _ ]) p fᴰ

    reindE-filler : {x y : Category.ob C} {f g : C [ x , y ]}
      {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      (p : f Eq.≡ g) (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
      → Path (Σ[ h ∈ C [ x , y ] ] Cᴰ.Hom[ h ][ xᴰ , yᴰ ])
          (f , fᴰ) (g , reindE p fᴰ)
    reindE-filler Eq.refl fᴰ = refl

  fromCategoryᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ'
  fromCategoryᴰ .ob[_] = Cᴰ.ob[_]
  fromCategoryᴰ .Hom[_][_,_] = Cᴰ.Hom[_][_,_]
  fromCategoryᴰ .idᴰ i ei = reindE ei Cᴰ.idᴰ
  fromCategoryᴰ .⋆ᴰ f g h e fᴰ gᴰ = reindE e (fᴰ Cᴰ.⋆ᴰ gᴰ)
  fromCategoryᴰ .⋆IdLᴰ i ei f e fᴰ = R.rectify $ R.≡out $
      sym (reindE-filler e _)
    ∙ R.⟨ sym (reindE-filler ei Cᴰ.idᴰ) ⟩⋆⟨ refl ⟩
    ∙ R.⋆IdL _
  fromCategoryᴰ .⋆IdRᴰ f i ei e fᴰ = R.rectify $ R.≡out $
      sym (reindE-filler e _)
    ∙ R.⟨ refl ⟩⋆⟨ sym (reindE-filler ei Cᴰ.idᴰ) ⟩
    ∙ R.⋆IdR _
  fromCategoryᴰ .⋆Assocᴰ f g h fg efg gh egh k e₁ e₂ fᴰ gᴰ hᴰ =
    R.rectify $ R.≡out $
      sym (reindE-filler e₁ _)
    ∙ R.⟨ sym (reindE-filler efg _) ⟩⋆⟨ refl ⟩
    ∙ R.⋆Assoc _ _ _
    ∙ R.⟨ refl ⟩⋆⟨ reindE-filler egh _ ⟩
    ∙ reindE-filler e₂ _
  fromCategoryᴰ .idᴰ-coh i i' ei ei' p = R.rectify $ R.≡out $
      sym (reindE-filler ei Cᴰ.idᴰ) ∙ reindE-filler ei' Cᴰ.idᴰ
  fromCategoryᴰ .⋆ᴰ-coh f g h h' e e' p fᴰ gᴰ = R.rectify $ R.≡out $
      sym (reindE-filler e _) ∙ reindE-filler e' _
  fromCategoryᴰ .isSetHomᴰ = Cᴰ.isSetHomᴰ

  -- THE PAYOFF OF THE Eq FORD.  `Eq.transport C refl b = b`, so the
  -- lifted operations COMPUTE wherever the ford is refl -- which is
  -- every place ∫ᶠ uses them.  Under the earlier Path-valued ford both
  -- of these FAILED, because `subst B refl b` is stuck for neutral B.
  fromCategoryᴰ-id-computes : {x : Category.ob C} {xᴰ : Cᴰ.ob[ x ]}
    → fromCategoryᴰ .idᴰ {xᴰ = xᴰ} (Category.id C) Eq.refl ≡ Cᴰ.idᴰ
  fromCategoryᴰ-id-computes = refl

  fromCategoryᴰ-⋆-computes : {x y z : Category.ob C}
    {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
    {f : C [ x , y ]} {g : C [ y , z ]}
    (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ.Hom[ g ][ yᴰ , zᴰ ])
    → fromCategoryᴰ .⋆ᴰ f g _ Eq.refl fᴰ gᴰ ≡ (fᴰ Cᴰ.⋆ᴰ gᴰ)
  fromCategoryᴰ-⋆-computes fᴰ gᴰ = refl
