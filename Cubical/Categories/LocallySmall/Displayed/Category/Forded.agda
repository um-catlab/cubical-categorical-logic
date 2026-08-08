{-
  FORDED DISPLAYED CATEGORIES, locally small.

  The level-indexed counterpart of Cubical.Categories.Displayed.Forded,
  displayed over Cubical.Categories.LocallySmall.Functor.Strict.

  WHY THIS EXISTS.  Level bookkeeping was never the hard part: Agda's
  level solver already makes `ℓ-max` associative, commutative and
  idempotent definitionally, so composing `Hom-ℓᴰ` along a functor is
  free.  What costs is the STRUCTURE -- reindexing along composite
  projections builds transports, and the two ways of associating a
  telescope differ.  Fording removes both:

    * `reindexS` has no `subst`, `transport` or `reind` in any field;
    * `reindexS SId` is the identity and `reindexS (G S∘ F)` is
      `reindexS F ∘ reindexS G`, both definitionally, both for
      variables.

  ORIENTATION, and why the ford is `Eq`-valued.  `idᴰ`/`⋆ᴰ` take their
  witnesses in the SAME direction `StrictFunctor`'s `F-id`/`F-seq`
  produce them, so `reindexS` hands each one over verbatim -- there is
  not one `sym` in this file.  That is what lets the ford be
  `Eq._≡_` rather than `Path`: `Eq.transport C Eq.refl b` REDUCES to
  `b`, while `subst B refl b` is STUCK whenever `B` is neutral.  So
  `fromCategoryᴰ` below lifts an existing `Categoryᴰ` and its `idᴰ`
  and `⋆ᴰ` still compute (`fromCategoryᴰ-id-computes`,
  `fromCategoryᴰ-⋆-computes`), which under a Path-valued ford they did
  not.  Strictness at variables and computation at `refl` are not in
  tension; the earlier appearance that they were came entirely from
  the fords pointing opposite ways.

  The level layer is where the ford is FREE.  `LEVEL` is
  `Indiscrete (Liftω Level)`, whose homs are `Unit`, so every ford
  witness over it is trivially inhabited and prop-valued, and the two
  coherence fields below are automatic.  `Categoryᴰ`'s existing
  `Homᴰ[_,_]` -- commented "convenient when displayed over an
  indiscrete category where the morphism f is uniquely determined" --
  is the hand-rolled special case of exactly this.

  TESTING AT Typeω.  You cannot state `x ≡ y` there, since Path is
  Type-valued.  Definitional equality is witnessed by `Coe` from
  Functor.Strict, inhabited by the identity precisely when the two
  sides are definitionally equal.
-}
module Cubical.Categories.LocallySmall.Displayed.Category.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Functor.Strict
open import Cubical.Categories.LocallySmall.Variables.Base

open Category
open Σω
open StrictFunctor

module _ (C : Category Cob CHom-ℓ) where
  private module C = CategoryNotation C

  record Categoryᶠᴰ (ob[_] : Cob → Typeω)
    (Hom-ℓᴰ : ∀ x y (xᴰ : ob[ x ]) (yᴰ : ob[ y ]) → Level) : Typeω where
    -- eta-equality is the DEFAULT and is load-bearing.  Do not add
    -- no-eta-equality: it is what makes two of these with
    -- definitionally equal fields definitionally equal.
    field
      Hom[_][_,_] : ∀ {x y} (f : C.Hom[ x , y ])
        (xᴰ : ob[ x ]) (yᴰ : ob[ y ]) → Type (Hom-ℓᴰ _ _ xᴰ yᴰ)

      idᴰ : ∀ {x} {xᴰ : ob[ x ]}
        (i : C.Hom[ x , x ]) → C.id Eq.≡ i → Hom[ i ][ xᴰ , xᴰ ]

      ⋆ᴰ : ∀ {x y z} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
        (f : C.Hom[ x , y ]) (g : C.Hom[ y , z ]) (h : C.Hom[ x , z ])
        → f C.⋆ g Eq.≡ h
        → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ h ][ xᴰ , zᴰ ]

      -- THE LAWS, homogeneous.  The stock locally small Categoryᴰ has
      -- to state these as `∫≡`, paths in the Σ of base and displayed
      -- hom; here the composite's base hom is a parameter and can be
      -- pinned, so they are ordinary equations.
      ⋆IdLᴰ : ∀ {x y} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
        (i : C.Hom[ x , x ]) (ei : C.id Eq.≡ i)
        (f : C.Hom[ x , y ]) (e : i C.⋆ f Eq.≡ f)
        (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        → ⋆ᴰ i f f e (idᴰ i ei) fᴰ ≡ fᴰ

      ⋆IdRᴰ : ∀ {x y} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
        (f : C.Hom[ x , y ]) (i : C.Hom[ y , y ]) (ei : C.id Eq.≡ i)
        (e : f C.⋆ i Eq.≡ f)
        (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        → ⋆ᴰ f i f e fᴰ (idᴰ i ei) ≡ fᴰ

      ⋆Assocᴰ : ∀ {w x y z}
        {wᴰ : ob[ w ]} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
        (f : C.Hom[ w , x ]) (g : C.Hom[ x , y ]) (h : C.Hom[ y , z ])
        (fg : C.Hom[ w , y ]) (efg : f C.⋆ g Eq.≡ fg)
        (gh : C.Hom[ x , z ]) (egh : g C.⋆ h Eq.≡ gh)
        (k : C.Hom[ w , z ]) (e₁ : fg C.⋆ h Eq.≡ k) (e₂ : f C.⋆ gh Eq.≡ k)
        (fᴰ : Hom[ f ][ wᴰ , xᴰ ]) (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
        (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
        → ⋆ᴰ fg h k e₁ (⋆ᴰ f g fg efg fᴰ gᴰ) hᴰ
          ≡ ⋆ᴰ f gh k e₂ fᴰ (⋆ᴰ g h gh egh gᴰ hᴰ)

      -- FORD COHERENCES: the ford is bookkeeping only.  Over LEVEL
      -- these are automatic, since its homs are Unit.
      idᴰ-coh : ∀ {x} {xᴰ : ob[ x ]}
        (i i' : C.Hom[ x , x ]) (ei : C.id Eq.≡ i) (ei' : C.id Eq.≡ i')
        (p : i ≡ i')
        → PathP (λ k → Hom[ p k ][ xᴰ , xᴰ ]) (idᴰ i ei) (idᴰ i' ei')

      ⋆ᴰ-coh : ∀ {x y z} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
        (f : C.Hom[ x , y ]) (g : C.Hom[ y , z ]) (h h' : C.Hom[ x , z ])
        (e : f C.⋆ g Eq.≡ h) (e' : f C.⋆ g Eq.≡ h') (p : h ≡ h')
        (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Hom[ g ][ yᴰ , zᴰ ])
        → PathP (λ k → Hom[ p k ][ xᴰ , zᴰ ])
            (⋆ᴰ f g h e fᴰ gᴰ) (⋆ᴰ f g h' e' fᴰ gᴰ)

      isSetHomᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ}
        → isSet Hom[ f ][ xᴰ , yᴰ ]

open Categoryᶠᴰ

-- ------------------------------------------------------------------
-- REINDEXING.  Every field hands the strict functor's own ford to the
-- displayed category's ford; the level function is composed with
-- F-ob, which Agda's level solver handles definitionally.
module _ {C : Category Cob CHom-ℓ} {D : Category Dob DHom-ℓ}
  (F : StrictFunctor C D)
  {obᴰ : Dob → Typeω}
  {Hom-ℓᴰ : ∀ x y (xᴰ : obᴰ x) (yᴰ : obᴰ y) → Level}
  (Dᴰ : Categoryᶠᴰ D obᴰ Hom-ℓᴰ) where

  reindexS : Categoryᶠᴰ C (λ x → obᴰ (F .F-ob x))
    (λ x y xᴰ yᴰ → Hom-ℓᴰ (F .F-ob x) (F .F-ob y) xᴰ yᴰ)
  reindexS .Hom[_][_,_] f xᴰ yᴰ = Dᴰ .Hom[_][_,_] (F .F-hom f) xᴰ yᴰ
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

-- reindexing is STRICTLY functorial, for variables, at Typeω.
module _ {C : Category Cob CHom-ℓ}
  {obᴰ : Cob → Typeω}
  {Hom-ℓᴰ : ∀ x y (xᴰ : obᴰ x) (yᴰ : obᴰ y) → Level}
  (Cᴰ : Categoryᶠᴰ C obᴰ Hom-ℓᴰ) where

  reindexS-Id : Coe (reindexS SId Cᴰ) Cᴰ
  reindexS-Id P x = x

module _ {C : Category Cob CHom-ℓ} {D : Category Dob DHom-ℓ}
  {E : Category Eob EHom-ℓ}
  (F : StrictFunctor C D) (G : StrictFunctor D E)
  {obᴰ : Eob → Typeω}
  {Hom-ℓᴰ : ∀ x y (xᴰ : obᴰ x) (yᴰ : obᴰ y) → Level}
  (Eᴰ : Categoryᶠᴰ E obᴰ Hom-ℓᴰ) where

  reindexS-comp : Coe (reindexS (G S∘ F) Eᴰ) (reindexS F (reindexS G Eᴰ))
  reindexS-comp P x = x

-- ------------------------------------------------------------------
-- THE TOTAL CATEGORY, and its display map as a STRICT functor.
module _ {C : Category Cob CHom-ℓ}
  {obᴰ : Cob → Typeω}
  {Hom-ℓᴰ : ∀ x y (xᴰ : obᴰ x) (yᴰ : obᴰ y) → Level}
  (Cᴰ : Categoryᶠᴰ C obᴰ Hom-ℓᴰ) where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᶠᴰ Cᴰ

  ∫ᶠ : Category (Σω[ x ∈ Cob ] obᴰ x)
    (λ xxᴰ yyᴰ → ℓ-max (CHom-ℓ (xxᴰ .fst) (yyᴰ .fst))
                       (Hom-ℓᴰ (xxᴰ .fst) (yyᴰ .fst) (xxᴰ .snd) (yyᴰ .snd)))
  ∫ᶠ .Hom[_,_] xxᴰ yyᴰ =
    Σ[ f ∈ C.Hom[ xxᴰ .fst , yyᴰ .fst ] ]
      Cᴰ.Hom[ f ][ xxᴰ .snd , yyᴰ .snd ]
  ∫ᶠ .id = C.id , Cᴰ.idᴰ C.id Eq.refl
  ∫ᶠ ._⋆_ (f , fᴰ) (g , gᴰ) =
    (f C.⋆ g) , Cᴰ.⋆ᴰ f g (f C.⋆ g) Eq.refl fᴰ gᴰ
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

  Fstᶠ : StrictFunctor ∫ᶠ C
  Fstᶠ .F-ob = fst
  Fstᶠ .F-hom = fst
  Fstᶠ .F-id f e = Eq.ap fst e
  Fstᶠ .F-seq f g h e = Eq.ap fst e

-- ------------------------------------------------------------------
-- EVERY locally small displayed category is a forded one.  This is
-- what makes the above usable rather than a fresh start: the existing
-- instances -- SET, SETᴰ, the graph and presheaf displayed categories
-- -- all lift, and the two ford coherences are discharged generically
-- by `rectify`, since a ford is a path in a hom-SET and any two agree.
open import Cubical.Categories.LocallySmall.Displayed.Category.Base
  using (Categoryᴰ)

module _ {C : Category Cob CHom-ℓ}
  {obᴰ : Cob → Typeω}
  {Hom-ℓᴰ : ∀ x y (xᴰ : obᴰ x) (yᴰ : obᴰ y) → Level}
  (Cᴰ : Categoryᴰ C obᴰ Hom-ℓᴰ) where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
    module ∫C = CategoryNotation Cᴰ.∫C

    -- An Eq-valued reind.  Unlike `Cᴰ.reind`, `Eq.transport _ Eq.refl b`
    -- REDUCES to `b`, so the lifted idᴰ/⋆ᴰ compute wherever the ford is
    -- refl -- which is everywhere ∫ᶠ and the fibres use them.
    reindE : ∀ {x y} {f g : C.Hom[ x , y ]} {xᴰ : obᴰ x} {yᴰ : obᴰ y}
      → f Eq.≡ g → Cᴰ.Hom[ f ][ xᴰ , yᴰ ] → Cᴰ.Hom[ g ][ xᴰ , yᴰ ]
    reindE p fᴰ = Eq.transport Cᴰ.Hom[_][ _ , _ ] p fᴰ

    reindE-filler : ∀ {x y} {f g : C.Hom[ x , y ]}
      {xᴰ : obᴰ x} {yᴰ : obᴰ y}
      (p : f Eq.≡ g) (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
      → Path Cᴰ.∫Hom[ _ , _ ] (f , fᴰ) (g , reindE p fᴰ)
    reindE-filler Eq.refl fᴰ = refl

  fromCategoryᴰ : Categoryᶠᴰ C obᴰ Hom-ℓᴰ
  fromCategoryᴰ .Hom[_][_,_] = Cᴰ.Hom[_][_,_]
  fromCategoryᴰ .idᴰ i ei = reindE ei Cᴰ.idᴰ
  fromCategoryᴰ .⋆ᴰ f g h e fᴰ gᴰ = reindE e (fᴰ Cᴰ.⋆ᴰ gᴰ)
  fromCategoryᴰ .⋆IdLᴰ i ei f e fᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      sym (reindE-filler e _)
    ∙ ∫C.⟨ sym (reindE-filler ei Cᴰ.idᴰ) ⟩⋆⟨⟩
    ∙ Cᴰ.⋆IdLᴰ fᴰ
  fromCategoryᴰ .⋆IdRᴰ f i ei e fᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      sym (reindE-filler e _)
    ∙ ∫C.⟨⟩⋆⟨ sym (reindE-filler ei Cᴰ.idᴰ) ⟩
    ∙ Cᴰ.⋆IdRᴰ fᴰ
  fromCategoryᴰ .⋆Assocᴰ f g h fg efg gh egh k e₁ e₂ fᴰ gᴰ hᴰ =
    Cᴰ.rectify $ Cᴰ.≡out $
      sym (reindE-filler e₁ _)
    ∙ ∫C.⟨ sym (reindE-filler efg _) ⟩⋆⟨⟩
    ∙ Cᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ
    ∙ ∫C.⟨⟩⋆⟨ reindE-filler egh _ ⟩
    ∙ reindE-filler e₂ _
  fromCategoryᴰ .idᴰ-coh i i' ei ei' p = Cᴰ.rectify $ Cᴰ.≡out $
      sym (reindE-filler ei Cᴰ.idᴰ) ∙ reindE-filler ei' Cᴰ.idᴰ
  fromCategoryᴰ .⋆ᴰ-coh f g h h' e e' p fᴰ gᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      sym (reindE-filler e _) ∙ reindE-filler e' _
  fromCategoryᴰ .isSetHomᴰ = Cᴰ.isSetHomᴰ

  -- THE PAYOFF OF THE Eq FORD.  `Eq.transport C Eq.refl b = b`, so the
  -- lifted operations COMPUTE wherever the ford is refl -- which is
  -- every place ∫ᶠ and `fibᶠ` use them.  Under a Path-valued ford both
  -- of these FAIL, because `subst B refl b` is stuck for neutral B.
  fromCategoryᴰ-id-computes : ∀ {x} {xᴰ : obᴰ x}
    → fromCategoryᴰ .idᴰ {xᴰ = xᴰ} C.id Eq.refl ≡ Cᴰ.idᴰ
  fromCategoryᴰ-id-computes = refl

  fromCategoryᴰ-⋆-computes : ∀ {x y z}
    {xᴰ : obᴰ x} {yᴰ : obᴰ y} {zᴰ : obᴰ z}
    {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]}
    (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ.Hom[ g ][ yᴰ , zᴰ ])
    → fromCategoryᴰ .⋆ᴰ f g _ Eq.refl fᴰ gᴰ ≡ (fᴰ Cᴰ.⋆ᴰ gᴰ)
  fromCategoryᴰ-⋆-computes fᴰ gᴰ = refl

-- ------------------------------------------------------------------
-- FREE LUNCH 1: PROP-VALUED HOMS.  If the displayed homs are
-- propositions -- which covers every PropertyOver / HomPropertyOver /
-- StructureOver-style displayed category, and anything cutting a
-- Cayley over-approximation down to the legitimate part -- then all
-- three laws AND both ford coherences are automatic.  You supply the
-- homs, the ford-taking idᴰ and ⋆ᴰ, and nothing else.
module _ {C : Category Cob CHom-ℓ}
  {obᴰ : Cob → Typeω}
  {Hom-ℓᴰ : ∀ x y (xᴰ : obᴰ x) (yᴰ : obᴰ y) → Level} where
  private module C = CategoryNotation C

  module _
    (H : ∀ {x y} (f : C.Hom[ x , y ]) (xᴰ : obᴰ x) (yᴰ : obᴰ y)
       → Type (Hom-ℓᴰ _ _ xᴰ yᴰ))
    (isPropH : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} → isProp (H f xᴰ yᴰ))
    (i[_][_] : ∀ {x} {xᴰ : obᴰ x}
       (i : C.Hom[ x , x ]) → C.id Eq.≡ i → H i xᴰ xᴰ)
    (s[_,_,_][_] : ∀ {x y z} {xᴰ : obᴰ x} {yᴰ : obᴰ y} {zᴰ : obᴰ z}
       (f : C.Hom[ x , y ]) (g : C.Hom[ y , z ]) (h : C.Hom[ x , z ])
       → f C.⋆ g Eq.≡ h → H f xᴰ yᴰ → H g yᴰ zᴰ → H h xᴰ zᴰ)
    where

    mkPropHomsᶠ : Categoryᶠᴰ C obᴰ Hom-ℓᴰ
    mkPropHomsᶠ .Hom[_][_,_] = H
    mkPropHomsᶠ .idᴰ = i[_][_]
    mkPropHomsᶠ .⋆ᴰ = s[_,_,_][_]
    mkPropHomsᶠ .⋆IdLᴰ _ _ _ _ _ = isPropH _ _
    mkPropHomsᶠ .⋆IdRᴰ _ _ _ _ _ = isPropH _ _
    mkPropHomsᶠ .⋆Assocᴰ _ _ _ _ _ _ _ _ _ _ _ _ _ = isPropH _ _
    mkPropHomsᶠ .idᴰ-coh _ _ _ _ p =
      isProp→PathP (λ _ → isPropH) _ _
    mkPropHomsᶠ .⋆ᴰ-coh _ _ _ _ _ _ p _ _ =
      isProp→PathP (λ _ → isPropH) _ _
    mkPropHomsᶠ .isSetHomᴰ = isProp→isSet isPropH

-- ------------------------------------------------------------------
-- FREE LUNCH 2: WEAKENING.  Extend any base by the objects of a fixed
-- category.  Every ford argument is ignored, so both coherences are
-- refl and the laws are the ambient category's.
module _ (C : Category Cob CHom-ℓ) (D : Category Dob DHom-ℓ) where
  private module D = CategoryNotation D

  weakenᶠ : Categoryᶠᴰ C (λ _ → Dob) (λ _ _ xᴰ yᴰ → DHom-ℓ xᴰ yᴰ)
  weakenᶠ .Hom[_][_,_] _ xᴰ yᴰ = D.Hom[ xᴰ , yᴰ ]
  weakenᶠ .idᴰ _ _ = D.id
  weakenᶠ .⋆ᴰ _ _ _ _ fᴰ gᴰ = fᴰ D.⋆ gᴰ
  weakenᶠ .⋆IdLᴰ _ _ _ _ = D.⋆IdL
  weakenᶠ .⋆IdRᴰ _ _ _ _ = D.⋆IdR
  weakenᶠ .⋆Assocᴰ _ _ _ _ _ _ _ _ _ _ fᴰ gᴰ hᴰ = D.⋆Assoc fᴰ gᴰ hᴰ
  weakenᶠ .idᴰ-coh _ _ _ _ _ = refl
  weakenᶠ .⋆ᴰ-coh _ _ _ _ _ _ _ _ _ = refl
  weakenᶠ .isSetHomᴰ = D.isSetHom

-- ------------------------------------------------------------------
-- FREE LUNCH 3: THE DIFFERENCE-LIST TELESCOPE, level-polymorphic.
--
-- A context former is not an OBJECT of the slice over C but an
-- OPERATION on it: given anything displayed over C by a strict
-- functor, it produces a further extension.  Concatenation then never
-- pulls anything back -- it asks the second former to build itself
-- over the first's output -- so it is composition of functions, hence
-- definitionally unital and associative in ANY association.
--
-- This is what the small-case version could not be: `at` must
-- quantify over the incoming category's own ob-type and level
-- function, which is exactly what the locally small setting provides.
record Ext (C : Category Cob CHom-ℓ) : Typeω₁ where
  field
    at-ob : ∀ {Eob : Typeω} {EHom-ℓ : Eob → Eob → Level}
      (E : Category Eob EHom-ℓ) → StrictFunctor E C → Typeω
    at-ℓ : ∀ {Eob : Typeω} {EHom-ℓ : Eob → Eob → Level}
      (E : Category Eob EHom-ℓ) (p : StrictFunctor E C)
      → at-ob E p → at-ob E p → Level
    at : ∀ {Eob : Typeω} {EHom-ℓ : Eob → Eob → Level}
      (E : Category Eob EHom-ℓ) (p : StrictFunctor E C)
      → Category (at-ob E p) (at-ℓ E p)
    disp : ∀ {Eob : Typeω} {EHom-ℓ : Eob → Eob → Level}
      (E : Category Eob EHom-ℓ) (p : StrictFunctor E C)
      → StrictFunctor (at E p) E

open Ext

-- definitional equality one universe up
Coe₁ : {A : Typeω₁} → A → A → Typeω₂
Coe₁ {A} x y = (P : A → Typeω₁) → P x → P y

module _ {C : Category Cob CHom-ℓ} where

  εE : Ext C
  εE .at-ob {Eob} E p = Eob
  εE .at-ℓ {EHom-ℓ = EHom-ℓ} E p = EHom-ℓ
  εE .at E p = E
  εE .disp E p = SId

  _·ᶠ_ : Ext C → Ext C → Ext C
  (Δ ·ᶠ Θ) .at-ob E p = Θ .at-ob (Δ .at E p) (p S∘ Δ .disp E p)
  (Δ ·ᶠ Θ) .at-ℓ  E p = Θ .at-ℓ  (Δ .at E p) (p S∘ Δ .disp E p)
  (Δ ·ᶠ Θ) .at    E p = Θ .at    (Δ .at E p) (p S∘ Δ .disp E p)
  (Δ ·ᶠ Θ) .disp  E p =
    Δ .disp E p S∘ Θ .disp (Δ .at E p) (p S∘ Δ .disp E p)

  -- CONCATENATION IS DEFINITIONALLY UNITAL AND ASSOCIATIVE, for
  -- variable telescopes.
  ext-lUnit : (Δ : Ext C) → Coe₁ (εE ·ᶠ Δ) Δ
  ext-lUnit Δ P x = x

  ext-rUnit : (Δ : Ext C) → Coe₁ (Δ ·ᶠ εE) Δ
  ext-rUnit Δ P x = x

  ext-assoc : (Δ Θ Ξ : Ext C) → Coe₁ ((Δ ·ᶠ Θ) ·ᶠ Ξ) (Δ ·ᶠ (Θ ·ᶠ Ξ))
  ext-assoc Δ Θ Ξ P x = x

  -- THE BRIDGE: every forded displayed category is a context former.
  module _ {obᴰ : Cob → Typeω}
    {Hom-ℓᴰ : ∀ x y (xᴰ : obᴰ x) (yᴰ : obᴰ y) → Level}
    (Cᴰ : Categoryᶠᴰ C obᴰ Hom-ℓᴰ) where

    ⌜_⌝ : Ext C
    ⌜_⌝ .at-ob {Eob} E p = Σω[ x ∈ Eob ] obᴰ (p .F-ob x)
    ⌜_⌝ .at-ℓ {EHom-ℓ = EHom-ℓ} E p xxᴰ yyᴰ =
      ℓ-max (EHom-ℓ (xxᴰ .fst) (yyᴰ .fst))
            (Hom-ℓᴰ (p .F-ob (xxᴰ .fst)) (p .F-ob (yyᴰ .fst))
                    (xxᴰ .snd) (yyᴰ .snd))
    ⌜_⌝ .at E p = ∫ᶠ (reindexS p Cᴰ)
    ⌜_⌝ .disp E p = Fstᶠ (reindexS p Cᴰ)
