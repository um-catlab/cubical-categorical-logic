{-# OPTIONS --lossy-unification #-}
{-

  THE SIMPLE TOTAL CATEGORY, FORDED.

  Instances.SimpleTotalCategoryR says that `C ×C D` is definitionally
  `∫C (weaken C D)`, so the "D on the right" simple total category is
  "just a type specialization of ∫Cᴰ", whereas the "D on the left" one
  has to be built by REINDEXING along `Sym`.  That asymmetry is an
  artefact of reindexing being transport-laden: it costs nothing to
  unfold a definition and a great deal to reindex.

  Over `Categoryᶠᴰ` (Displayed.Forded) reindexing builds no data ---
  `reindexS` just hands the functor's ford to the displayed category's
  ford --- and is strictly functorial.  So here BOTH sides are one
  definition, `∫ᶠs`, applied to two different strict functors out of
  the product, and

      ∫ᶠsl Cᴰ ≡ ∫ᶠsr (reindexS Symᶠ Cᴰ)         -- refl
      Fstᶠsl Cᴰ ≡ Fstᶠsr (reindexS Symᶠ Cᴰ)     -- refl

  The re-associator `Assoc : Functor (∫C ∫Cᴰsr) (∫C Cᴰ)` that R.agda
  abandons as `{!!}` is `Assocᶠs` below, again one definition serving
  both sides.  Generically, `Assocᶠ` is an isomorphism: it is the
  identity on objects and morphisms on the nose (Σ-eta), and both
  composites are `SId` (`Assoc-sec`, `Assoc-ret`).

  WITH THE Eq-VALUED FORD the re-associator got strictly better: its
  two law fields are now just `Eq.ap`, because the ford `∫ᶠ Cᴰ` builds
  for a pinned base hom is produced by PATTERN MATCHING (`idFordᶠ`,
  `⋆Fordᶠ` below) and hence REDUCES to `Eq.refl` at `Eq.refl`.  Under
  the Path-valued ford the corresponding terms were `idᴰ-coh`/`⋆ᴰ-coh`
  chains.  Same for `∫ᶠ→∫C`, which is now the identity in all four
  fields because `fromCategoryᴰ` computes.

  See .Unforded for the un-forded versions of the two abandoned
  functors --- they are definable too, so the gain here is uniformity,
  not definability.

-}
module Cubical.Categories.Displayed.Instances.SimpleTotalCategory.Forded
  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base using (Functor)
open import Cubical.Categories.Instances.BinProduct using (_×C_)
open import Cubical.Categories.Instances.TotalCategory.Base using (∫C)
open import Cubical.Categories.Functors.Strict.Base
open import Cubical.Categories.Displayed.Base using (Categoryᴰ)
open import Cubical.Categories.Displayed.Forded

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

open StrictFunctor
open Categoryᶠᴰ

-- ------------------------------------------------------------------
-- A ford is a PROP.  `x Eq.≡ y` is equivalent to `x ≡ y`, so in a
-- hom-set any two fords agree.  This is what lets the law fields of a
-- `StrictFunctor` be moved when its ob/hom parts already agree.
isPropEqHom : {A : Category ℓC ℓC'} {x y : Category.ob A}
  {f g : A [ x , y ]} → isProp (f Eq.≡ g)
isPropEqHom {A = A} {f = f} {g = g} =
  subst isProp (Eq.PathPathEq {x = f} {y = g}) (Category.isSetHom A f g)

-- ------------------------------------------------------------------
-- WEAKENING, forded.  Every law is D's own law, verbatim: the ford is
-- discarded because the displayed hom does not mention the base hom
-- at all, which is also why both coherences are `refl`.
module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  private
    module D = Category D

  weakenᶠ : Categoryᶠᴰ C ℓD ℓD'
  weakenᶠ .ob[_] _ = D.ob
  weakenᶠ .Hom[_][_,_] _ d d' = D [ d , d' ]
  weakenᶠ .idᴰ _ _ = D.id
  weakenᶠ .⋆ᴰ _ _ _ _ dᴰ eᴰ = dᴰ D.⋆ eᴰ
  weakenᶠ .⋆IdLᴰ _ _ _ _ fᴰ = D.⋆IdL fᴰ
  weakenᶠ .⋆IdRᴰ _ _ _ _ fᴰ = D.⋆IdR fᴰ
  weakenᶠ .⋆Assocᴰ _ _ _ _ _ _ _ _ _ _ fᴰ gᴰ hᴰ = D.⋆Assoc fᴰ gᴰ hᴰ
  weakenᶠ .idᴰ-coh _ _ _ _ _ = refl
  weakenᶠ .⋆ᴰ-coh _ _ _ _ _ _ _ _ _ = refl
  weakenᶠ .isSetHomᴰ = D.isSetHom

-- the forded product of categories
_×ᶠ_ : (C : Category ℓC ℓC') (D : Category ℓD ℓD')
     → Category (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
C ×ᶠ D = ∫ᶠ (weakenᶠ C D)

infixr 5 _×ᶠ_

-- ------------------------------------------------------------------
-- LIFTING A FORD TO THE TOTAL CATEGORY.  `∫ᶠ Cᴰ` builds its id and
-- its composite with the ford `Eq.refl`, so a ford downstairs lifts
-- BY PATTERN MATCHING, and `idFordᶠ Cᴰ _ Eq.refl` REDUCES to
-- `Eq.refl`.  That reduction is what makes `Assocᶠ` below a plain
-- `Eq.ap`; with a Path-valued ford these would have been
-- `idᴰ-coh`/`⋆ᴰ-coh` terms, stuck at `refl`.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module ∫Cᴰ = Category (∫ᶠ Cᴰ)

  idFordᶠ : {x : C.ob} {xᴰ : Cᴰ.ob[ x ]}
    (i : C [ x , x ]) (ei : C.id Eq.≡ i)
    → ∫Cᴰ.id {x = x , xᴰ} Eq.≡ (i , Cᴰ.idᴰ i ei)
  idFordᶠ i Eq.refl = Eq.refl

  ⋆Fordᶠ : {x y z : C.ob}
    {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
    (f : C [ x , y ]) (g : C [ y , z ]) (h : C [ x , z ])
    (e : f C.⋆ g Eq.≡ h)
    (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ.Hom[ g ][ yᴰ , zᴰ ])
    → ∫Cᴰ._⋆_ (f , fᴰ) (g , gᴰ) Eq.≡ (h , Cᴰ.⋆ᴰ f g h e fᴰ gᴰ)
  ⋆Fordᶠ f g h Eq.refl fᴰ gᴰ = Eq.refl

  -- both compute
  idFordᶠ-refl : {x : C.ob} {xᴰ : Cᴰ.ob[ x ]}
    → idFordᶠ {xᴰ = xᴰ} C.id Eq.refl ≡ Eq.refl
  idFordᶠ-refl = refl

  ⋆Fordᶠ-refl : {x y z : C.ob}
    {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
    {f : C [ x , y ]} {g : C [ y , z ]}
    (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ.Hom[ g ][ yᴰ , zᴰ ])
    → ⋆Fordᶠ f g (f C.⋆ g) Eq.refl fᴰ gᴰ ≡ Eq.refl
  ⋆Fordᶠ-refl fᴰ gᴰ = refl

-- ------------------------------------------------------------------
-- THE DISPLAYED TOTAL CATEGORY, forded.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ')
  (Cᴰᴰ : Categoryᶠᴰ (∫ᶠ Cᴰ) ℓDᴰ ℓDᴰ') where
  private
    module C = Category C
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module Cᴰᴰ = Categoryᶠᴰ Cᴰᴰ
    module ∫Cᴰ = Category (∫ᶠ Cᴰ)

  ∫ᶠᴰ : Categoryᶠᴰ C (ℓ-max ℓCᴰ ℓDᴰ) (ℓ-max ℓCᴰ' ℓDᴰ')
  ∫ᶠᴰ .ob[_] x = Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] Cᴰᴰ.ob[ (x , xᴰ) ]
  ∫ᶠᴰ .Hom[_][_,_] f (xᴰ , xᴰᴰ) (yᴰ , yᴰᴰ) =
    Σ[ fᴰ ∈ Cᴰ.Hom[ f ][ xᴰ , yᴰ ] ] Cᴰᴰ.Hom[ (f , fᴰ) ][ xᴰᴰ , yᴰᴰ ]
  ∫ᶠᴰ .idᴰ i ei =
    Cᴰ.idᴰ i ei , Cᴰᴰ.idᴰ (i , Cᴰ.idᴰ i ei) (idFordᶠ Cᴰ i ei)
  ∫ᶠᴰ .⋆ᴰ f g h e (fᴰ , fᴰᴰ) (gᴰ , gᴰᴰ) =
    Cᴰ.⋆ᴰ f g h e fᴰ gᴰ ,
    Cᴰᴰ.⋆ᴰ (f , fᴰ) (g , gᴰ) (h , Cᴰ.⋆ᴰ f g h e fᴰ gᴰ)
      (⋆Fordᶠ Cᴰ f g h e fᴰ gᴰ) fᴰᴰ gᴰᴰ
  ∫ᶠᴰ .⋆IdLᴰ i ei f e (fᴰ , fᴰᴰ) = ΣPathP
    ( Cᴰ.⋆IdLᴰ i ei f e fᴰ
    , Cᴰᴰ.⋆ᴰ-coh (i , Cᴰ.idᴰ i ei) (f , fᴰ)
        (f , Cᴰ.⋆ᴰ i f f e (Cᴰ.idᴰ i ei) fᴰ) (f , fᴰ)
        (⋆Fordᶠ Cᴰ i f f e (Cᴰ.idᴰ i ei) fᴰ)
        idL-ford
        (ΣPathP (refl , Cᴰ.⋆IdLᴰ i ei f e fᴰ))
        (Cᴰᴰ.idᴰ (i , Cᴰ.idᴰ i ei) (idFordᶠ Cᴰ i ei))
        fᴰᴰ
      ▷ Cᴰᴰ.⋆IdLᴰ (i , Cᴰ.idᴰ i ei) (idFordᶠ Cᴰ i ei)
          (f , fᴰ) idL-ford fᴰᴰ )
    where
    idL-ford : ∫Cᴰ._⋆_ (i , Cᴰ.idᴰ i ei) (f , fᴰ) Eq.≡ (f , fᴰ)
    idL-ford = Eq.pathToEq (ΣPathP
      ( Eq.eqToPath e
      , Cᴰ.⋆ᴰ-coh i f (i C.⋆ f) f Eq.refl e (Eq.eqToPath e)
          (Cᴰ.idᴰ i ei) fᴰ
        ▷ Cᴰ.⋆IdLᴰ i ei f e fᴰ ))
  ∫ᶠᴰ .⋆IdRᴰ f i ei e (fᴰ , fᴰᴰ) = ΣPathP
    ( Cᴰ.⋆IdRᴰ f i ei e fᴰ
    , Cᴰᴰ.⋆ᴰ-coh (f , fᴰ) (i , Cᴰ.idᴰ i ei)
        (f , Cᴰ.⋆ᴰ f i f e fᴰ (Cᴰ.idᴰ i ei)) (f , fᴰ)
        (⋆Fordᶠ Cᴰ f i f e fᴰ (Cᴰ.idᴰ i ei))
        idR-ford
        (ΣPathP (refl , Cᴰ.⋆IdRᴰ f i ei e fᴰ))
        fᴰᴰ
        (Cᴰᴰ.idᴰ (i , Cᴰ.idᴰ i ei) (idFordᶠ Cᴰ i ei))
      ▷ Cᴰᴰ.⋆IdRᴰ (f , fᴰ) (i , Cᴰ.idᴰ i ei) (idFordᶠ Cᴰ i ei)
          idR-ford fᴰᴰ )
    where
    idR-ford : ∫Cᴰ._⋆_ (f , fᴰ) (i , Cᴰ.idᴰ i ei) Eq.≡ (f , fᴰ)
    idR-ford = Eq.pathToEq (ΣPathP
      ( Eq.eqToPath e
      , Cᴰ.⋆ᴰ-coh f i (f C.⋆ i) f Eq.refl e (Eq.eqToPath e)
          fᴰ (Cᴰ.idᴰ i ei)
        ▷ Cᴰ.⋆IdRᴰ f i ei e fᴰ ))
  ∫ᶠᴰ .⋆Assocᴰ f g h fg efg gh egh k e₁ e₂
      (fᴰ , fᴰᴰ) (gᴰ , gᴰᴰ) (hᴰ , hᴰᴰ) = ΣPathP
    ( α
    , Cᴰᴰ.⋆Assocᴰ (f , fᴰ) (g , gᴰ) (h , hᴰ)
        (fg , fgᴰ) fg-ford (gh , ghᴰ) gh-ford
        (k , kᴰL) k-ford₁ k-ford₂ fᴰᴰ gᴰᴰ hᴰᴰ
      ◁ Cᴰᴰ.⋆ᴰ-coh (f , fᴰ) (gh , ghᴰ) (k , kᴰL) (k , kᴰR)
          k-ford₂ k-ford₃ (ΣPathP (refl , α)) fᴰᴰ
          (Cᴰᴰ.⋆ᴰ (g , gᴰ) (h , hᴰ) (gh , ghᴰ) gh-ford gᴰᴰ hᴰᴰ) )
    where
    fgᴰ = Cᴰ.⋆ᴰ f g fg efg fᴰ gᴰ
    ghᴰ = Cᴰ.⋆ᴰ g h gh egh gᴰ hᴰ
    kᴰL = Cᴰ.⋆ᴰ fg h k e₁ fgᴰ hᴰ
    kᴰR = Cᴰ.⋆ᴰ f gh k e₂ fᴰ ghᴰ
    α : kᴰL ≡ kᴰR
    α = Cᴰ.⋆Assocᴰ f g h fg efg gh egh k e₁ e₂ fᴰ gᴰ hᴰ
    fg-ford = ⋆Fordᶠ Cᴰ f g fg efg fᴰ gᴰ
    gh-ford = ⋆Fordᶠ Cᴰ g h gh egh gᴰ hᴰ
    k-ford₁ = ⋆Fordᶠ Cᴰ fg h k e₁ fgᴰ hᴰ
    k-ford₃ = ⋆Fordᶠ Cᴰ f gh k e₂ fᴰ ghᴰ
    k-ford₂ : ∫Cᴰ._⋆_ (f , fᴰ) (gh , ghᴰ) Eq.≡ (k , kᴰL)
    k-ford₂ = Eq.pathToEq (ΣPathP
      ( Eq.eqToPath e₂
      , Cᴰ.⋆ᴰ-coh f gh (f C.⋆ gh) k Eq.refl e₂ (Eq.eqToPath e₂) fᴰ ghᴰ
        ▷ sym α ))
  ∫ᶠᴰ .idᴰ-coh i i' ei ei' p = ΣPathP
    ( q
    , Cᴰᴰ.idᴰ-coh (i , Cᴰ.idᴰ i ei) (i' , Cᴰ.idᴰ i' ei')
        (idFordᶠ Cᴰ i ei) (idFordᶠ Cᴰ i' ei') (ΣPathP (p , q)) )
    where
    q = Cᴰ.idᴰ-coh i i' ei ei' p
  ∫ᶠᴰ .⋆ᴰ-coh f g h h' e e' p (fᴰ , fᴰᴰ) (gᴰ , gᴰᴰ) = ΣPathP
    ( q
    , Cᴰᴰ.⋆ᴰ-coh (f , fᴰ) (g , gᴰ)
        (h , Cᴰ.⋆ᴰ f g h e fᴰ gᴰ) (h' , Cᴰ.⋆ᴰ f g h' e' fᴰ gᴰ)
        (⋆Fordᶠ Cᴰ f g h e fᴰ gᴰ) (⋆Fordᶠ Cᴰ f g h' e' fᴰ gᴰ)
        (ΣPathP (p , q)) fᴰᴰ gᴰᴰ )
    where
    q = Cᴰ.⋆ᴰ-coh f g h h' e e' p fᴰ gᴰ
  ∫ᶠᴰ .isSetHomᴰ = isSetΣ Cᴰ.isSetHomᴰ (λ _ → Cᴰᴰ.isSetHomᴰ)

  -- ----------------------------------------------------------------
  -- THE RE-ASSOCIATOR.  `∫ᶠ (∫ᶠᴰ Cᴰ Cᴰᴰ)` and `∫ᶠ Cᴰᴰ` have the same
  -- underlying data up to Σ-eta.  With the Eq ford they also have the
  -- same id and the same composite ON THE NOSE, because the fords
  -- `∫ᶠᴰ` feeds to `Cᴰᴰ` are `idFordᶠ _ Eq.refl` and
  -- `⋆Fordᶠ _ _ _ Eq.refl _ _`, which REDUCE to `Eq.refl`.  So both
  -- law fields are a plain `Eq.ap`.
  private
    module ∫∫ = Category (∫ᶠ ∫ᶠᴰ)
    module ∫ᴰᴰ = Category (∫ᶠ Cᴰᴰ)

    aOb : ∫∫.ob → ∫ᴰᴰ.ob
    aOb z = (z .fst , z .snd .fst) , z .snd .snd

    aHom : {x y : ∫∫.ob} → ∫ᶠ ∫ᶠᴰ [ x , y ] → ∫ᶠ Cᴰᴰ [ aOb x , aOb y ]
    aHom m = (m .fst , m .snd .fst) , m .snd .snd

    a⁻Ob : ∫ᴰᴰ.ob → ∫∫.ob
    a⁻Ob z = z .fst .fst , z .fst .snd , z .snd

    a⁻Hom : {x y : ∫ᴰᴰ.ob} → ∫ᶠ Cᴰᴰ [ x , y ] → ∫ᶠ ∫ᶠᴰ [ a⁻Ob x , a⁻Ob y ]
    a⁻Hom m = m .fst .fst , m .fst .snd , m .snd

  -- the two total categories agree on id and on composition, on the
  -- nose.  Under the Path-valued ford neither of these was `refl`.
  Assoc-id : {x : ∫∫.ob} → aHom (∫∫.id {x = x}) ≡ ∫ᴰᴰ.id
  Assoc-id = refl

  Assoc-seq : {x y z : ∫∫.ob}
    (f : ∫ᶠ ∫ᶠᴰ [ x , y ]) (g : ∫ᶠ ∫ᶠᴰ [ y , z ])
    → aHom (∫∫._⋆_ f g) ≡ ∫ᴰᴰ._⋆_ (aHom f) (aHom g)
  Assoc-seq f g = refl

  Assocᶠ : StrictFunctor (∫ᶠ ∫ᶠᴰ) (∫ᶠ Cᴰᴰ)
  Assocᶠ .F-ob = aOb
  Assocᶠ .F-hom = aHom
  Assocᶠ .F-id m e = Eq.ap aHom e
  Assocᶠ .F-seq f g h e = Eq.ap aHom e

  Assocᶠ⁻ : StrictFunctor (∫ᶠ Cᴰᴰ) (∫ᶠ ∫ᶠᴰ)
  Assocᶠ⁻ .F-ob = a⁻Ob
  Assocᶠ⁻ .F-hom = a⁻Hom
  Assocᶠ⁻ .F-id m e = Eq.ap a⁻Hom e
  Assocᶠ⁻ .F-seq f g h e = Eq.ap a⁻Hom e

  -- the two composites are the identity ON THE NOSE for objects and
  -- morphisms; only the two law fields have to be moved, and a ford
  -- in a hom-set is a prop.
  Assoc-ob-sec : (z : ∫∫.ob) → a⁻Ob (aOb z) ≡ z
  Assoc-ob-sec z = refl

  Assoc-hom-sec : {x y : ∫∫.ob} (m : ∫ᶠ ∫ᶠᴰ [ x , y ])
    → a⁻Hom (aHom m) ≡ m
  Assoc-hom-sec m = refl

  Assoc-ob-ret : (z : ∫ᴰᴰ.ob) → aOb (a⁻Ob z) ≡ z
  Assoc-ob-ret z = refl

  Assoc-hom-ret : {x y : ∫ᴰᴰ.ob} (m : ∫ᶠ Cᴰᴰ [ x , y ])
    → aHom (a⁻Hom m) ≡ m
  Assoc-hom-ret m = refl

  Assoc-sec : (Assocᶠ⁻ S∘ Assocᶠ) ≡ SId
  Assoc-sec i .F-ob z = z
  Assoc-sec i .F-hom m = m
  Assoc-sec i .F-id m e =
    isPropEqHom {A = ∫ᶠ ∫ᶠᴰ} ((Assocᶠ⁻ S∘ Assocᶠ) .F-id m e) e i
  Assoc-sec i .F-seq f g h e =
    isPropEqHom {A = ∫ᶠ ∫ᶠᴰ} ((Assocᶠ⁻ S∘ Assocᶠ) .F-seq f g h e) e i

  Assoc-ret : (Assocᶠ S∘ Assocᶠ⁻) ≡ SId
  Assoc-ret i .F-ob z = z
  Assoc-ret i .F-hom m = m
  Assoc-ret i .F-id m e =
    isPropEqHom {A = ∫ᶠ Cᴰᴰ} ((Assocᶠ S∘ Assocᶠ⁻) .F-id m e) e i
  Assoc-ret i .F-seq f g h e =
    isPropEqHom {A = ∫ᶠ Cᴰᴰ} ((Assocᶠ S∘ Assocᶠ⁻) .F-seq f g h e) e i

-- ------------------------------------------------------------------
-- FORGETTING A REINDEXING on total categories.  `reindexS` builds no
-- data, so this projection is the identity on the displayed part.
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : StrictFunctor C D) (Dᴰ : Categoryᶠᴰ D ℓDᴰ ℓDᴰ') where
  private
    module C = Category C
    module D = Category D
    module Dᴰ = Categoryᶠᴰ Dᴰ
    module ∫F = Category (∫ᶠ (reindexS F Dᴰ))
    module ∫D = Category (∫ᶠ Dᴰ)

    fOb : ∫F.ob → ∫D.ob
    fOb z = F .F-ob (z .fst) , z .snd

    fHom : {x y : ∫F.ob} → ∫ᶠ (reindexS F Dᴰ) [ x , y ]
         → ∫ᶠ Dᴰ [ fOb x , fOb y ]
    fHom m = F .F-hom (m .fst) , m .snd

  forgetReindexᶠ : StrictFunctor (∫ᶠ (reindexS F Dᴰ)) (∫ᶠ Dᴰ)
  forgetReindexᶠ .F-ob = fOb
  forgetReindexᶠ .F-hom = fHom
  forgetReindexᶠ .F-id m e =
    idFordᶠ Dᴰ (F .F-hom C.id) (F .F-id C.id Eq.refl) Eq.∙ Eq.ap fHom e
  forgetReindexᶠ .F-seq f g h e =
    ⋆Fordᶠ Dᴰ (F .F-hom (f .fst)) (F .F-hom (g .fst)) _
      (F .F-seq (f .fst) (g .fst) (f .fst C.⋆ g .fst) Eq.refl)
      (f .snd) (g .snd)
    Eq.∙ Eq.ap fHom e

-- ------------------------------------------------------------------
-- THE BRIDGE TO THE STOCK PRODUCT.  `C ×C D` is by definition
-- `∫C (weaken C D)`, and `C ×ᶠ D` is `∫ᶠ (weakenᶠ C D)`: the ob, hom,
-- id and composition of the two agree definitionally, only the law
-- fields differ (and `Category` is `no-eta-equality`, so the two are
-- not the same term).  These two strict functors are the identity in
-- ALL FOUR fields, and compose to `SId` on the nose both ways.
module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  ×ᶠ→×C : StrictFunctor (C ×ᶠ D) (C ×C D)
  ×ᶠ→×C .F-ob z = z
  ×ᶠ→×C .F-hom m = m
  ×ᶠ→×C .F-id f e = e
  ×ᶠ→×C .F-seq f g h e = e

  ×C→×ᶠ : StrictFunctor (C ×C D) (C ×ᶠ D)
  ×C→×ᶠ .F-ob z = z
  ×C→×ᶠ .F-hom m = m
  ×C→×ᶠ .F-id f e = e
  ×C→×ᶠ .F-seq f g h e = e

  ×-bridge-sec : (×C→×ᶠ S∘ ×ᶠ→×C) ≡ SId
  ×-bridge-sec = refl

  ×-bridge-ret : (×ᶠ→×C S∘ ×C→×ᶠ) ≡ SId
  ×-bridge-ret = refl

-- SYMMETRY of the product, as a strict functor.
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  Symᶠ : StrictFunctor (C ×C D) (D ×C C)
  Symᶠ .F-ob z = z .snd , z .fst
  Symᶠ .F-hom m = m .snd , m .fst
  Symᶠ .F-id f e = Eq.ap (λ z → z .snd , z .fst) e
  Symᶠ .F-seq f g h e = Eq.ap (λ z → z .snd , z .fst) e

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  private
    Sym² = Symᶠ {C = D} {D = C} S∘ Symᶠ {C = C} {D = D}

  -- Symᶠ is involutive on objects and morphisms on the nose...
  Symᶠ-invol-ob : (z : Category.ob (C ×C D)) → Sym² .F-ob z ≡ z
  Symᶠ-invol-ob z = refl

  Symᶠ-invol-hom : {x y : Category.ob (C ×C D)} (m : (C ×C D) [ x , y ])
    → Sym² .F-hom m ≡ m
  Symᶠ-invol-hom m = refl

  -- ...but NOT in the law fields: they are `Eq.ap swap (Eq.ap swap e)`,
  -- and `Eq.ap` is stuck on a neutral witness.  Under the Path ford
  -- these were `sym (sym e)`, which computes, so `Symᶠ-invol` used to
  -- be `refl`.  It is still true, just not definitionally.
  Symᶠ-invol : Sym² ≡ SId
  Symᶠ-invol i .F-ob z = z
  Symᶠ-invol i .F-hom m = m
  Symᶠ-invol i .F-id f e = isPropEqHom {A = C ×C D} (Sym² .F-id f e) e i
  Symᶠ-invol i .F-seq f g h e =
    isPropEqHom {A = C ×C D} (Sym² .F-seq f g h e) e i

-- ------------------------------------------------------------------
-- THE SIMPLE TOTAL CATEGORY.
--
-- One definition, parameterised by the strict functor out of the
-- product along which the displayed category is read.  `R` takes that
-- functor to be the (identity-on-data) bridge into `C ×C D`; `L`
-- takes it to be the bridge followed by `Symᶠ`.  Nothing else
-- differs, because `reindexS` builds no data: THIS is where the L/R
-- asymmetry of the un-forded development disappears.
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where

  module _ {B : Category ℓB ℓB'} (F : StrictFunctor (C ×ᶠ D) B)
    (Bᴰ : Categoryᶠᴰ B ℓCᴰ ℓCᴰ') where

    ∫ᶠs : Categoryᶠᴰ C (ℓ-max ℓD ℓCᴰ) (ℓ-max ℓD' ℓCᴰ')
    ∫ᶠs = ∫ᶠᴰ (weakenᶠ C D) (reindexS F Bᴰ)

    -- the display map of the simple total category onto the product
    Fstᶠs : StrictFunctor (∫ᶠ ∫ᶠs) (C ×ᶠ D)
    Fstᶠs = Fstᶠ (reindexS F Bᴰ) S∘ Assocᶠ (weakenᶠ C D) (reindexS F Bᴰ)

    -- THE RE-ASSOCIATOR that was left as a hole.
    Assocᶠs : StrictFunctor (∫ᶠ ∫ᶠs) (∫ᶠ Bᴰ)
    Assocᶠs = forgetReindexᶠ F Bᴰ S∘ Assocᶠ (weakenᶠ C D) (reindexS F Bᴰ)

  -- R: D on the right of the product
  ∫ᶠsr : Categoryᶠᴰ (C ×C D) ℓCᴰ ℓCᴰ'
       → Categoryᶠᴰ C (ℓ-max ℓD ℓCᴰ) (ℓ-max ℓD' ℓCᴰ')
  ∫ᶠsr Cᴰ = ∫ᶠs (×ᶠ→×C C D) Cᴰ

  Fstᶠsr : (Cᴰ : Categoryᶠᴰ (C ×C D) ℓCᴰ ℓCᴰ')
    → StrictFunctor (∫ᶠ (∫ᶠsr Cᴰ)) (C ×ᶠ D)
  Fstᶠsr Cᴰ = Fstᶠs (×ᶠ→×C C D) Cᴰ

  Assocᶠsr : (Cᴰ : Categoryᶠᴰ (C ×C D) ℓCᴰ ℓCᴰ')
    → StrictFunctor (∫ᶠ (∫ᶠsr Cᴰ)) (∫ᶠ Cᴰ)
  Assocᶠsr Cᴰ = Assocᶠs (×ᶠ→×C C D) Cᴰ

  -- L: D on the left of the product
  ∫ᶠsl : Categoryᶠᴰ (D ×C C) ℓCᴰ ℓCᴰ'
       → Categoryᶠᴰ C (ℓ-max ℓD ℓCᴰ) (ℓ-max ℓD' ℓCᴰ')
  ∫ᶠsl Cᴰ = ∫ᶠs (Symᶠ S∘ ×ᶠ→×C C D) Cᴰ

  Fstᶠsl : (Cᴰ : Categoryᶠᴰ (D ×C C) ℓCᴰ ℓCᴰ')
    → StrictFunctor (∫ᶠ (∫ᶠsl Cᴰ)) (C ×ᶠ D)
  Fstᶠsl Cᴰ = Fstᶠs (Symᶠ S∘ ×ᶠ→×C C D) Cᴰ

  Assocᶠsl : (Cᴰ : Categoryᶠᴰ (D ×C C) ℓCᴰ ℓCᴰ')
    → StrictFunctor (∫ᶠ (∫ᶠsl Cᴰ)) (∫ᶠ Cᴰ)
  Assocᶠsl Cᴰ = Assocᶠs (Symᶠ S∘ ×ᶠ→×C C D) Cᴰ

  -- L IS R, precomposed with one strict reindexing.  `reindexS` is
  -- strictly functorial, so this is `refl` --- contrast the un-forded
  -- development, where `∫Cᴰsl` is `∫Cᴰsr` of an `EqReindex` and the
  -- corresponding statement is not available.
  sl-is-sr : (Cᴰ : Categoryᶠᴰ (D ×C C) ℓCᴰ ℓCᴰ')
    → ∫ᶠsl Cᴰ ≡ ∫ᶠsr (reindexS Symᶠ Cᴰ)
  sl-is-sr Cᴰ = refl

  Fst-sl-is-sr : (Cᴰ : Categoryᶠᴰ (D ×C C) ℓCᴰ ℓCᴰ')
    → Fstᶠsl Cᴰ ≡ Fstᶠsr (reindexS Symᶠ Cᴰ)
  Fst-sl-is-sr Cᴰ = refl

  -- ...and so does the re-associator, up to the two law fields, which
  -- are fords in a hom-set, hence props.
  Assoc-sl-factors : (Cᴰ : Categoryᶠᴰ (D ×C C) ℓCᴰ ℓCᴰ')
    → Assocᶠsl Cᴰ
    ≡ (forgetReindexᶠ Symᶠ Cᴰ S∘ Assocᶠsr (reindexS Symᶠ Cᴰ))
  Assoc-sl-factors Cᴰ i .F-ob = Assocᶠsl Cᴰ .F-ob
  Assoc-sl-factors Cᴰ i .F-hom = Assocᶠsl Cᴰ .F-hom
  Assoc-sl-factors Cᴰ i .F-id m e = isPropEqHom {A = ∫ᶠ Cᴰ}
    (Assocᶠsl Cᴰ .F-id m e)
    ((forgetReindexᶠ Symᶠ Cᴰ S∘ Assocᶠsr (reindexS Symᶠ Cᴰ)) .F-id m e) i
  Assoc-sl-factors Cᴰ i .F-seq f g h e = isPropEqHom {A = ∫ᶠ Cᴰ}
    (Assocᶠsl Cᴰ .F-seq f g h e)
    ((forgetReindexᶠ Symᶠ Cᴰ S∘ Assocᶠsr (reindexS Symᶠ Cᴰ))
      .F-seq f g h e) i

-- ------------------------------------------------------------------
-- PLUGGING THE EXISTING LIBRARY IN.  `fromCategoryᴰ` makes every
-- stock `Categoryᴰ` forded, and the forded total category maps onto
-- the stock one, so the re-associator can be shipped as an ordinary
-- `Functor` landing in `∫C Cᴰ` --- which is the type the abandoned
-- `Assoc` in Instances.SimpleTotalCategoryR was asking for.
--
-- With the Eq ford `fromCategoryᴰ` COMPUTES at `Eq.refl`, so the two
-- total categories now share id and composition on the nose and
-- `∫ᶠ→∫C` is the identity in all four fields.  Under the Path ford it
-- needed two `reind-filler`s.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module ∫f = Category (∫ᶠ (fromCategoryᴰ Cᴰ))
    module ∫s = Category (∫C Cᴰ)

  ∫ᶠ-id-computes : {x : C.ob} {xᴰ : Cᴰ.ob[ x ]}
    → ∫f.id {x = x , xᴰ} ≡ ∫s.id {x = x , xᴰ}
  ∫ᶠ-id-computes = refl

  ∫ᶠ-seq-computes : {x y z : ∫f.ob}
    (f : ∫ᶠ (fromCategoryᴰ Cᴰ) [ x , y ]) (g : ∫ᶠ (fromCategoryᴰ Cᴰ) [ y , z ])
    → ∫f._⋆_ f g ≡ ∫s._⋆_ f g
  ∫ᶠ-seq-computes f g = refl

  ∫ᶠ→∫C : StrictFunctor (∫ᶠ (fromCategoryᴰ Cᴰ)) (∫C Cᴰ)
  ∫ᶠ→∫C .F-ob z = z
  ∫ᶠ→∫C .F-hom m = m
  ∫ᶠ→∫C .F-id m e = e
  ∫ᶠ→∫C .F-seq f g h e = e

-- R: the displayed category lives over `C ×C D`.
module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD')
  (Cᴰ : Categoryᴰ (C ×C D) ℓCᴰ ℓCᴰ') where

  ∫ᴰsrᶠ : Categoryᶠᴰ C (ℓ-max ℓD ℓCᴰ) (ℓ-max ℓD' ℓCᴰ')
  ∫ᴰsrᶠ = ∫ᶠsr {C = C} {D = D} (fromCategoryᴰ Cᴰ)

  -- THE FUNCTOR THAT WAS `{!!}`.
  Assocsr : Functor (∫ᶠ ∫ᴰsrᶠ) (∫C Cᴰ)
  Assocsr = Strict→Fun
    (∫ᶠ→∫C Cᴰ S∘ Assocᶠsr {C = C} {D = D} (fromCategoryᴰ Cᴰ))

-- L: the displayed category lives over `D ×C C`.  Same definition,
-- one extra `reindexS`.
module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD')
  (Cᴰ : Categoryᴰ (D ×C C) ℓCᴰ ℓCᴰ') where

  ∫ᴰslᶠ : Categoryᶠᴰ C (ℓ-max ℓD ℓCᴰ) (ℓ-max ℓD' ℓCᴰ')
  ∫ᴰslᶠ = ∫ᶠsl {C = C} {D = D} (fromCategoryᴰ Cᴰ)

  -- THE FUNCTOR THAT WAS COMMENTED OUT IN SimpleTotalCategoryL.
  Assocsl⁻ : Functor (∫ᶠ ∫ᴰslᶠ) (∫C Cᴰ)
  Assocsl⁻ = Strict→Fun
    (∫ᶠ→∫C Cᴰ S∘ Assocᶠsl {C = C} {D = D} (fromCategoryᴰ Cᴰ))
