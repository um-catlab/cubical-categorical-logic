{-# OPTIONS --lossy-unification #-}
{-

  FORDED DISPLAYED PRESHEAVES.

  The presheaf counterpart of Cubical.Categories.Displayed.Forded.

  A `Presheafᴰ P Cᴰ ℓPᴰ` is a family `p[ p ][ xᴰ ]` with an action
  `_⋆ᴰ_ : Cᴰ [ f ][ xᴰ , yᴰ ] → p[ g ][ yᴰ ] → p[ f ⋆ g ][ xᴰ ]`.
  The composite's index is BUILT, so every derived operation that
  wants the result at a different index has to `reind` along a path in
  `P.p[ x ]`, and every law about it is a PathP that has to be
  `rectify`d.  That is where the `reind`/`rectify` traffic in
  Displayed/Presheaf/* comes from.

  Fording the action --- taking the target index `h` and a witness
  `f ⋆ g Eq.≡ h` as arguments --- removes both.  The ford is Eq-valued
  and oriented FORWARDS (composite on the left, target on the right),
  exactly as `Categoryᶠᴰ.⋆ᴰ` and `StrictFunctor.F-seq` are, which is
  what lets every reindexing hand the witness over verbatim with no
  `sym` --- and hence what lets the ford be `Eq`, whose transport
  computes at `refl`.

  1. THE LAWS ARE HOMOGENEOUS.  `⋆IdLᴰ` and `⋆Assocᴰ` below are
     ordinary equations, not PathPs, because the target index is a
     parameter that can be pinned to whatever the other side lives
     over.

  2. THE DERIVED OPERATIONS ARE TRANSPORT-FREE.  Every combinator in
     `PresheafᶠᴰNotation`/`PresheafⱽᶠNotation` --- `_⋆ⱽᴰ_`,
     `⋆Assocⱽⱽᴰ`, `⋆Assocᴰⱽᴰ`, `⋆Assocⱽᴰᴰ`, `⋆ⱽIdL`, `_⋆ᴰⱽ_`,
     `⋆Assocᴰᴰⱽ` --- is a single field application with no `reind` and
     no `rectify`.  The same seven in Displayed.Presheaf.Base cost 13
     `reind`/`reind-filler`s and 2 `rectify`s, and three of them can
     only be stated as paths in the total presheaf `∫P` rather than as
     equations.

  3. REINDEXING IS STRICTLY FUNCTORIAL, along an Eq-forded presheaf
     morphism `PshHomᶠ`: `reindᶠ idPshHomᶠ Pᴰ ≡ Pᴰ` and
     `reindᶠ (α ⋆PshHomᶠ β) Rᴰ ≡ reindᶠ α (reindᶠ β Rᴰ)`, both by
     `refl`, both for variables.  This is the reindexing that
     Displayed.Instances.Presheaf.Eq.Base has to route through
     `Cubical.Data.Equality` precisely because the path-based version
     does not compute.

     `PshHomᶠ` is the Eq-forded analogue of `PshHomStrict`, and it has
     to be: `PshHomStrict.N-hom` has a PATH ford, so reindexing along
     it must insert `Eq.pathToEq ∘ Eq.eqToPath`, which is not the
     identity definitionally.  See `reindᶠStrict-Id-FAILS` at the
     bottom, where that is exhibited rather than asserted.

  4. THE BRIDGE COMPUTES.  `fromPresheafᴰ` turns any stock `Presheafᴰ`
     into a forded one, using `Eq.transport` for the reindexing.  Since
     `Eq.transport C Eq.refl b = b` REDUCES, the lifted action computes
     at the identity ford: `fromPresheafᴰ-⋆-computes` is `refl`.  Under
     the earlier Path-valued ford it was not, because `subst B refl b`
     is stuck for neutral `B`.

  Reindexing along a `StrictFunctor` of the base is transport-free too
  (`reindexSPshᶠᴰ`), but is NOT strictly functorial, for a reason that
  has nothing to do with the displayed data; see the note there.

-}
module Cubical.Categories.Displayed.Presheaf.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Functors.Strict.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Forded
open import Cubical.Categories.Displayed.Presheaf.Base
import Cubical.Categories.Displayed.Reasoning as Reasoning

private
  variable
    ℓC ℓC' ℓD ℓD' ℓᴰ ℓᴰ' ℓP ℓQ ℓR ℓPᴰ ℓQᴰ ℓRᴰ : Level

open StrictFunctor

-- ------------------------------------------------------------------
-- Eq-FORDED PRESHEAF MORPHISMS.  The presheaf-level analogue of
-- `StrictFunctor`, with the ford oriented forwards so that composition
-- and reindexing pass it along verbatim.
record PshHomᶠ {C : Category ℓC ℓC'}
  (P : Presheaf C ℓP) (Q : Presheaf C ℓQ)
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓP ℓQ)) where
  private
    module C = Category C
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  field
    N-ob : (x : C.ob) → P.p[ x ] → Q.p[ x ]
    N-hom : {x y : C.ob} (f : C [ x , y ])
      (g : P.p[ y ]) (h : P.p[ x ])
      → f P.⋆ g Eq.≡ h
      → f Q.⋆ N-ob y g Eq.≡ N-ob x h

open PshHomᶠ

module _ {C : Category ℓC ℓC'} {P : Presheaf C ℓP} where
  idPshHomᶠ : PshHomᶠ P P
  idPshHomᶠ .N-ob x p = p
  idPshHomᶠ .N-hom f g h e = e

module _ {C : Category ℓC ℓC'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} {R : Presheaf C ℓR} where
  infixr 9 _⋆PshHomᶠ_
  _⋆PshHomᶠ_ : PshHomᶠ P Q → PshHomᶠ Q R → PshHomᶠ P R
  (α ⋆PshHomᶠ β) .N-ob x p = β .N-ob x (α .N-ob x p)
  (α ⋆PshHomᶠ β) .N-hom {x} {y} f g h e =
    β .N-hom f (α .N-ob y g) (α .N-ob x h) (α .N-hom f g h e)

module _ {C : Category ℓC ℓC'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} {R : Presheaf C ℓR}
  (α : PshHomᶠ P Q) (β : PshHomᶠ Q R) where
  -- unital and associative for VARIABLES, exactly as `_S∘_` is
  ⋆PshHomᶠIdL : idPshHomᶠ ⋆PshHomᶠ α ≡ α
  ⋆PshHomᶠIdL = refl

  ⋆PshHomᶠIdR : α ⋆PshHomᶠ idPshHomᶠ ≡ α
  ⋆PshHomᶠIdR = refl

-- the stock Path-forded morphisms embed, at the cost of a
-- `pathToEq`/`eqToPath` round trip
module _ {C : Category ℓC ℓC'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} where
  open PshHomStrict

  fromPshHomStrict : PshHomStrict P Q → PshHomᶠ P Q
  fromPshHomStrict α .N-ob = α .N-ob
  fromPshHomStrict α .N-hom {x} {y} f g h e =
    Eq.pathToEq (α .N-hom x y f g h (Eq.eqToPath e))

-- ------------------------------------------------------------------
-- THE DEFINITION.  eta-equality is the DEFAULT and is load-bearing;
-- do not add no-eta-equality.
record Presheafᶠᴰ {C : Category ℓC ℓC'} (P : Presheaf C ℓP)
  (Cᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ') (ℓPᴰ : Level)
  : Type (ℓ-max (ℓ-max ℓC ℓC')
           (ℓ-max (ℓ-max ℓᴰ ℓᴰ') (ℓ-max ℓP (ℓ-suc ℓPᴰ)))) where
  private
    module C = Category C
    module P = PresheafNotation P
    module Cᴰ = Categoryᶠᴰ Cᴰ
  field
    p[_][_] : {x : C.ob} → P.p[ x ] → Cᴰ.ob[ x ] → Type ℓPᴰ

    ⋆ᴰ : {x y : C.ob} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      (f : C [ x , y ]) (g : P.p[ y ]) (h : P.p[ x ])
      → f P.⋆ g Eq.≡ h
      → Cᴰ.Hom[ f ][ xᴰ , yᴰ ] → p[ g ][ yᴰ ] → p[ h ][ xᴰ ]

    -- THE LAWS, homogeneous: not a PathP in sight.
    ⋆IdLᴰ : {x : C.ob} {xᴰ : Cᴰ.ob[ x ]}
      (i : C [ x , x ]) (ei : C.id Eq.≡ i)
      (g : P.p[ x ]) (e : i P.⋆ g Eq.≡ g)
      (gᴰ : p[ g ][ xᴰ ])
      → ⋆ᴰ i g g e (Cᴰ.idᴰ i ei) gᴰ ≡ gᴰ

    ⋆Assocᴰ : {x y z : C.ob}
      {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
      (f : C [ x , y ]) (g : C [ y , z ]) (h : P.p[ z ])
      (fg : C [ x , z ]) (efg : f C.⋆ g Eq.≡ fg)
      (gh : P.p[ y ]) (egh : g P.⋆ h Eq.≡ gh)
      (k : P.p[ x ]) (e₁ : fg P.⋆ h Eq.≡ k) (e₂ : f P.⋆ gh Eq.≡ k)
      (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ.Hom[ g ][ yᴰ , zᴰ ])
      (hᴰ : p[ h ][ zᴰ ])
      → ⋆ᴰ fg h k e₁ (Cᴰ.⋆ᴰ f g fg efg fᴰ gᴰ) hᴰ
        ≡ ⋆ᴰ f gh k e₂ fᴰ (⋆ᴰ g h gh egh gᴰ hᴰ)

    -- FORD COHERENCE: the witness is bookkeeping only.  Eq fords, but
    -- a Path index `q` and a PathP conclusion, as in `Categoryᶠᴰ`.
    -- This is what lets `∫Pᶠ` be built, since there the action lands
    -- over `f ⋆ g` with witness `Eq.refl` rather than over a pinned
    -- target.
    ⋆ᴰ-coh : {x y : C.ob} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      (f : C [ x , y ]) (g : P.p[ y ]) (h h' : P.p[ x ])
      (e : f P.⋆ g Eq.≡ h) (e' : f P.⋆ g Eq.≡ h') (q : h ≡ h')
      (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : p[ g ][ yᴰ ])
      → PathP (λ k → p[ q k ][ xᴰ ])
          (⋆ᴰ f g h e fᴰ gᴰ) (⋆ᴰ f g h' e' fᴰ gᴰ)

    isSetPshᴰ : {x : C.ob} {g : P.p[ x ]} {xᴰ : Cᴰ.ob[ x ]}
      → isSet p[ g ][ xᴰ ]

-- ------------------------------------------------------------------
-- DERIVED NOTATION.  Every operation and every law below is a single
-- field application: no `reind`, no `reind-filler`, no `rectify`.
module PresheafᶠᴰNotation {C : Category ℓC ℓC'} {P : Presheaf C ℓP}
  {Cᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ'} (Pᴰ : Presheafᶠᴰ P Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module P = PresheafNotation P
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module PF = Presheafᶠᴰ Pᴰ

  p[_][_] : {x : C.ob} → P.p[ x ] → Cᴰ.ob[ x ] → Type ℓPᴰ
  p[ g ][ xᴰ ] = PF.p[ g ][ xᴰ ]

  isSetPshᴰ : {x : C.ob} {g : P.p[ x ]} {xᴰ : Cᴰ.ob[ x ]}
    → isSet p[ g ][ xᴰ ]
  isSetPshᴰ = PF.isSetPshᴰ

  -- vertical homs of the base displayed category
  vᴰ[_,_] : {x : C.ob} → Cᴰ.ob[ x ] → Cᴰ.ob[ x ] → Type ℓᴰ'
  vᴰ[ xᴰ , yᴰ ] = Cᴰ.Hom[ Category.id C ][ xᴰ , yᴰ ]

  idᶠᴰ : {x : C.ob} {xᴰ : Cᴰ.ob[ x ]} → vᴰ[ xᴰ , xᴰ ]
  idᶠᴰ = Cᴰ.idᴰ C.id Eq.refl

  infixr 9 _⋆ᶠᴰ_ _⋆ⱽᴰ_

  -- the unforded action, recovered by taking the witness `Eq.refl`
  _⋆ᶠᴰ_ : {x y : C.ob} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
    {f : C [ x , y ]} {g : P.p[ y ]}
    → Cᴰ.Hom[ f ][ xᴰ , yᴰ ] → p[ g ][ yᴰ ] → p[ f P.⋆ g ][ xᴰ ]
  _⋆ᶠᴰ_ {f = f} {g = g} fᴰ gᴰ = PF.⋆ᴰ f g (f P.⋆ g) Eq.refl fᴰ gᴰ

  -- THE VERTICAL ACTION.  Displayed.Presheaf.Base needs
  -- `reind (P.⋆IdL _)` here; the ford absorbs it.
  _⋆ⱽᴰ_ : {x : C.ob} {xᴰ xᴰ' : Cᴰ.ob[ x ]} {g : P.p[ x ]}
    → vᴰ[ xᴰ , xᴰ' ] → p[ g ][ xᴰ' ] → p[ g ][ xᴰ ]
  _⋆ⱽᴰ_ {g = g} fⱽ gᴰ =
    PF.⋆ᴰ C.id g g (Eq.pathToEq (P.⋆IdL g)) fⱽ gᴰ

  -- vertical composition in the base
  _⋆ⱽ_ : {x : C.ob} {xᴰ xᴰ' xᴰ'' : Cᴰ.ob[ x ]}
    → vᴰ[ xᴰ , xᴰ' ] → vᴰ[ xᴰ' , xᴰ'' ] → vᴰ[ xᴰ , xᴰ'' ]
  fⱽ ⋆ⱽ gⱽ =
    Cᴰ.⋆ᴰ C.id C.id C.id (Eq.pathToEq (C.⋆IdL C.id)) fⱽ gⱽ

  _⋆ᴰⱽ'_ : {x y : C.ob} {xᴰ : Cᴰ.ob[ x ]} {yᴰ yᴰ' : Cᴰ.ob[ y ]}
    {f : C [ x , y ]}
    → Cᴰ.Hom[ f ][ xᴰ , yᴰ ] → vᴰ[ yᴰ , yᴰ' ] → Cᴰ.Hom[ f ][ xᴰ , yᴰ' ]
  _⋆ᴰⱽ'_ {f = f} fᴰ gⱽ =
    Cᴰ.⋆ᴰ f C.id f (Eq.pathToEq (C.⋆IdR f)) fᴰ gⱽ

  _⋆ⱽᴰ'_ : {x y : C.ob} {xᴰ xᴰ' : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
    {g : C [ x , y ]}
    → vᴰ[ xᴰ , xᴰ' ] → Cᴰ.Hom[ g ][ xᴰ' , yᴰ ] → Cᴰ.Hom[ g ][ xᴰ , yᴰ ]
  _⋆ⱽᴰ'_ {g = g} fⱽ gᴰ =
    Cᴰ.⋆ᴰ C.id g g (Eq.pathToEq (C.⋆IdL g)) fⱽ gᴰ

  -- THE LAWS.  All homogeneous, all one field application.
  ⋆ⱽIdL : {x : C.ob} {xᴰ : Cᴰ.ob[ x ]} {g : P.p[ x ]}
    → (gᴰ : p[ g ][ xᴰ ]) → idᶠᴰ ⋆ⱽᴰ gᴰ ≡ gᴰ
  ⋆ⱽIdL {g = g} gᴰ =
    PF.⋆IdLᴰ C.id Eq.refl g (Eq.pathToEq (P.⋆IdL g)) gᴰ

  ⋆IdLᶠᴰ : {x : C.ob} {xᴰ : Cᴰ.ob[ x ]} {g : P.p[ x ]}
    → (gᴰ : p[ g ][ xᴰ ]) → PathP (λ k → p[ P.⋆IdL g k ][ xᴰ ])
        (idᶠᴰ ⋆ᶠᴰ gᴰ) gᴰ
  ⋆IdLᶠᴰ {g = g} gᴰ =
    PF.⋆ᴰ-coh C.id g (C.id P.⋆ g) g Eq.refl
      (Eq.pathToEq (P.⋆IdL g)) (P.⋆IdL g) idᶠᴰ gᴰ
    ▷ ⋆ⱽIdL gᴰ

  ⋆Assocⱽⱽᴰ : {x : C.ob} {xᴰ xᴰ' xᴰ'' : Cᴰ.ob[ x ]} {h : P.p[ x ]}
    (fⱽ : vᴰ[ xᴰ , xᴰ' ]) (gⱽ : vᴰ[ xᴰ' , xᴰ'' ]) (hᴰ : p[ h ][ xᴰ'' ])
    → (fⱽ ⋆ⱽ gⱽ) ⋆ⱽᴰ hᴰ ≡ fⱽ ⋆ⱽᴰ (gⱽ ⋆ⱽᴰ hᴰ)
  ⋆Assocⱽⱽᴰ {h = h} fⱽ gⱽ hᴰ =
    PF.⋆Assocᴰ C.id C.id h C.id (Eq.pathToEq (C.⋆IdL C.id))
      h (Eq.pathToEq (P.⋆IdL h))
      h (Eq.pathToEq (P.⋆IdL h)) (Eq.pathToEq (P.⋆IdL h)) fⱽ gⱽ hᴰ

  ⋆Assocᴰⱽᴰ : {x y : C.ob} {xᴰ : Cᴰ.ob[ x ]} {yᴰ yᴰ' : Cᴰ.ob[ y ]}
    {f : C [ x , y ]} {h : P.p[ y ]}
    (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) (gⱽ : vᴰ[ yᴰ , yᴰ' ])
    (hᴰ : p[ h ][ yᴰ' ])
    → (fᴰ ⋆ᴰⱽ' gⱽ) ⋆ᶠᴰ hᴰ ≡ fᴰ ⋆ᶠᴰ (gⱽ ⋆ⱽᴰ hᴰ)
  ⋆Assocᴰⱽᴰ {f = f} {h = h} fᴰ gⱽ hᴰ =
    PF.⋆Assocᴰ f C.id h f (Eq.pathToEq (C.⋆IdR f))
      h (Eq.pathToEq (P.⋆IdL h))
      (f P.⋆ h) Eq.refl Eq.refl fᴰ gⱽ hᴰ

  ⋆Assocⱽᴰᴰ : {x y : C.ob} {xᴰ xᴰ' : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
    {g : C [ x , y ]} {h : P.p[ y ]}
    (fⱽ : vᴰ[ xᴰ , xᴰ' ]) (gᴰ : Cᴰ.Hom[ g ][ xᴰ' , yᴰ ])
    (hᴰ : p[ h ][ yᴰ ])
    → (fⱽ ⋆ⱽᴰ' gᴰ) ⋆ᶠᴰ hᴰ ≡ fⱽ ⋆ⱽᴰ (gᴰ ⋆ᶠᴰ hᴰ)
  ⋆Assocⱽᴰᴰ {g = g} {h = h} fⱽ gᴰ hᴰ =
    PF.⋆Assocᴰ C.id g h g (Eq.pathToEq (C.⋆IdL g)) (g P.⋆ h) Eq.refl
      (g P.⋆ h) Eq.refl (Eq.pathToEq (P.⋆IdL (g P.⋆ h))) fⱽ gᴰ hᴰ

  ⋆Assocᶠᴰ : {x y z : C.ob}
    {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
    {f : C [ x , y ]} {g : C [ y , z ]} {h : P.p[ z ]}
    (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ.Hom[ g ][ yᴰ , zᴰ ])
    (hᴰ : p[ h ][ zᴰ ])
    → PathP (λ k → p[ P.⋆Assoc f g h k ][ xᴰ ])
        ((Cᴰ.⋆ᴰ f g (f C.⋆ g) Eq.refl fᴰ gᴰ) ⋆ᶠᴰ hᴰ)
        (fᴰ ⋆ᶠᴰ (gᴰ ⋆ᶠᴰ hᴰ))
  ⋆Assocᶠᴰ {f = f} {g = g} {h = h} fᴰ gᴰ hᴰ =
    PF.⋆Assocᴰ f g h (f C.⋆ g) Eq.refl (g P.⋆ h) Eq.refl
      ((f C.⋆ g) P.⋆ h) Eq.refl
      (Eq.pathToEq (sym (P.⋆Assoc f g h))) fᴰ gᴰ hᴰ
    ◁ PF.⋆ᴰ-coh f (g P.⋆ h) ((f C.⋆ g) P.⋆ h) (f P.⋆ (g P.⋆ h))
        (Eq.pathToEq (sym (P.⋆Assoc f g h))) Eq.refl (P.⋆Assoc f g h)
        fᴰ (gᴰ ⋆ᶠᴰ hᴰ)

-- ------------------------------------------------------------------
-- VERTICAL PRESHEAVES: displayed over a representable.
module PresheafⱽᶠNotation {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ'} {c : Category.ob C}
  (Pᴰ : Presheafᶠᴰ (C [-, c ]) Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module PF = Presheafᶠᴰ Pᴰ
  open PresheafᶠᴰNotation Pᴰ public

  pⱽ[_] : Cᴰ.ob[ c ] → Type ℓPᴰ
  pⱽ[ cᴰ ] = p[ C.id ][ cᴰ ]

  -- Displayed.Presheaf.Base needs `reind (C.⋆IdR _)` here.
  _⋆ᴰⱽ_ : {x : C.ob} {xᴰ : Cᴰ.ob[ x ]} {cᴰ : Cᴰ.ob[ c ]}
    {f : C [ x , c ]}
    → Cᴰ.Hom[ f ][ xᴰ , cᴰ ] → pⱽ[ cᴰ ] → p[ f ][ xᴰ ]
  _⋆ᴰⱽ_ {f = f} fᴰ pⱽ =
    PF.⋆ᴰ f C.id f (Eq.pathToEq (C.⋆IdR f)) fᴰ pⱽ

  ⋆Assocᴰᴰⱽ : {x y : C.ob} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
    {cᴰ : Cᴰ.ob[ c ]} {f : C [ x , y ]} {g : C [ y , c ]}
    (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ.Hom[ g ][ yᴰ , cᴰ ])
    (pⱽ : pⱽ[ cᴰ ])
    → (Cᴰ.⋆ᴰ f g (f C.⋆ g) Eq.refl fᴰ gᴰ) ⋆ᴰⱽ pⱽ
      ≡ fᴰ ⋆ᶠᴰ (gᴰ ⋆ᴰⱽ pⱽ)
  ⋆Assocᴰᴰⱽ {f = f} {g = g} fᴰ gᴰ pⱽ =
    PF.⋆Assocᴰ f g C.id (f C.⋆ g) Eq.refl g (Eq.pathToEq (C.⋆IdR g))
      (f C.⋆ g) (Eq.pathToEq (C.⋆IdR (f C.⋆ g))) Eq.refl fᴰ gᴰ pⱽ

-- ------------------------------------------------------------------
-- A REAL INSTANCE: the representable displayed presheaf.  Every field
-- is literally a field of `Cᴰ`.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ')
  {c : Category.ob C} where
  private
    module Cᴰ = Categoryᶠᴰ Cᴰ
  open Presheafᶠᴰ

  _[-][-,_]ᶠ : Cᴰ.ob[ c ] → Presheafᶠᴰ (C [-, c ]) Cᴰ ℓᴰ'
  (_[-][-,_]ᶠ cᴰ) .p[_][_] f xᴰ = Cᴰ.Hom[ f ][ xᴰ , cᴰ ]
  (_[-][-,_]ᶠ cᴰ) .⋆ᴰ = Cᴰ.⋆ᴰ
  (_[-][-,_]ᶠ cᴰ) .⋆IdLᴰ = Cᴰ.⋆IdLᴰ
  (_[-][-,_]ᶠ cᴰ) .⋆Assocᴰ = Cᴰ.⋆Assocᴰ
  (_[-][-,_]ᶠ cᴰ) .⋆ᴰ-coh = Cᴰ.⋆ᴰ-coh
  (_[-][-,_]ᶠ cᴰ) .isSetPshᴰ = Cᴰ.isSetHomᴰ

-- ------------------------------------------------------------------
-- REINDEXING along an Eq-forded presheaf morphism.  No transport and
-- no `sym`: the morphism's ford goes straight into the displayed
-- presheaf's ford.
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
  (α : PshHomᶠ P Q) (Qᴰ : Presheafᶠᴰ Q Cᴰ ℓQᴰ) where
  open Presheafᶠᴰ

  reindᶠ : Presheafᶠᴰ P Cᴰ ℓQᴰ
  reindᶠ .p[_][_] {x = x} p xᴰ = Qᴰ .p[_][_] (α .N-ob x p) xᴰ
  reindᶠ .⋆ᴰ {x = x} {y = y} f g h e fᴰ gᴰ =
    Qᴰ .⋆ᴰ f (α .N-ob y g) (α .N-ob x h) (α .N-hom f g h e) fᴰ gᴰ
  reindᶠ .⋆IdLᴰ {x = x} i ei g e gᴰ =
    Qᴰ .⋆IdLᴰ i ei (α .N-ob x g) (α .N-hom i g g e) gᴰ
  reindᶠ .⋆Assocᴰ {x = x} {y = y} {z = z}
    f g h fg efg gh egh k e₁ e₂ fᴰ gᴰ hᴰ =
    Qᴰ .⋆Assocᴰ f g (α .N-ob z h) fg efg
      (α .N-ob y gh) (α .N-hom g h gh egh)
      (α .N-ob x k) (α .N-hom fg h k e₁) (α .N-hom f gh k e₂)
      fᴰ gᴰ hᴰ
  reindᶠ .⋆ᴰ-coh {x = x} {y = y} f g h h' e e' q fᴰ gᴰ =
    Qᴰ .⋆ᴰ-coh f (α .N-ob y g) (α .N-ob x h) (α .N-ob x h')
      (α .N-hom f g h e) (α .N-hom f g h' e')
      (cong (α .N-ob x) q) fᴰ gᴰ
  reindᶠ .isSetPshᴰ = Qᴰ .isSetPshᴰ

-- REINDEXING IS STRICTLY FUNCTORIAL, for variables.
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP} (Pᴰ : Presheafᶠᴰ P Cᴰ ℓPᴰ) where
  reindᶠ-Id : reindᶠ idPshHomᶠ Pᴰ ≡ Pᴰ
  reindᶠ-Id = refl

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} {R : Presheaf C ℓR}
  (α : PshHomᶠ P Q) (β : PshHomᶠ Q R)
  (Rᴰ : Presheafᶠᴰ R Cᴰ ℓRᴰ) where
  reindᶠ-comp : reindᶠ (α ⋆PshHomᶠ β) Rᴰ ≡ reindᶠ α (reindᶠ β Rᴰ)
  reindᶠ-comp = refl

-- ------------------------------------------------------------------
-- THE TOTAL PRESHEAF.  A forded displayed presheaf assembles into a
-- genuine presheaf on `∫ᶠ Cᴰ`, so representability of a forded
-- displayed presheaf is a `UniversalElement (∫ᶠ Cᴰ) (∫Pᶠ Pᴰ)` --- no
-- bespoke universal-property record is introduced anywhere here.
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP} (Pᴰ : Presheafᶠᴰ P Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module P = PresheafNotation P
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module Pᴰ = PresheafᶠᴰNotation Pᴰ
  open Functor

  ∫Pᶠ : Presheaf (∫ᶠ Cᴰ) (ℓ-max ℓP ℓPᴰ)
  ∫Pᶠ .F-ob (x , xᴰ) .fst = Σ[ g ∈ P.p[ x ] ] Pᴰ.p[ g ][ xᴰ ]
  ∫Pᶠ .F-ob (x , xᴰ) .snd = isSetΣ P.isSetPsh (λ _ → Pᴰ.isSetPshᴰ)
  ∫Pᶠ .F-hom (f , fᴰ) (g , gᴰ) = (f P.⋆ g) , (fᴰ Pᴰ.⋆ᶠᴰ gᴰ)
  ∫Pᶠ .F-id = funExt λ (g , gᴰ) → ΣPathP (P.⋆IdL g , Pᴰ.⋆IdLᶠᴰ gᴰ)
  ∫Pᶠ .F-seq (f , fᴰ) (g , gᴰ) = funExt λ (h , hᴰ) →
    ΣPathP (P.⋆Assoc g f h , Pᴰ.⋆Assocᶠᴰ gᴰ fᴰ hᴰ)

-- ------------------------------------------------------------------
-- REINDEXING ALONG A STRICT FUNCTOR of the base.  Also transport-free,
-- and with the re-oriented fords also `sym`-free --- note that
-- `⋆ᴰ-coh` does not even change the ford, since the index path lives
-- in the base presheaf, which is untouched.
--
-- This is NOT strictly functorial, and the obstruction is entirely in
-- the BASE presheaf: `Q ∘F (Strict→Fun SId ^opF)` has the same `F-ob`
-- and `F-hom` as `Q` but builds `F-id`/`F-seq` out of
-- `Eq.eqToPath (Eq.sym …)` composed with `_∙_` by `_∘F_`, so it is not
-- definitionally `Q` and the two sides do not even have the same type.
-- Re-checked against the new `Strict→Fun`; see `reindexS-base-FAILS`.
-- Fording `Presheaf` itself would fix it by the same argument as
-- `reindexS-Id`.
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : StrictFunctor C D) {Dᴰ : Categoryᶠᴰ D ℓᴰ ℓᴰ'}
  {Q : Presheaf D ℓQ} (Qᴰ : Presheafᶠᴰ Q Dᴰ ℓQᴰ) where
  open Presheafᶠᴰ

  reindexSPshᶠᴰ :
    Presheafᶠᴰ (Q ∘F ((Strict→Fun F) ^opF)) (reindexS F Dᴰ) ℓQᴰ
  reindexSPshᶠᴰ .p[_][_] = Qᴰ .p[_][_]
  reindexSPshᶠᴰ .⋆ᴰ f g h e fᴰ gᴰ = Qᴰ .⋆ᴰ (F .F-hom f) g h e fᴰ gᴰ
  reindexSPshᶠᴰ .⋆IdLᴰ i ei g e gᴰ =
    Qᴰ .⋆IdLᴰ (F .F-hom i) (F .F-id i ei) g e gᴰ
  reindexSPshᶠᴰ .⋆Assocᴰ f g h fg efg gh egh k e₁ e₂ fᴰ gᴰ hᴰ =
    Qᴰ .⋆Assocᴰ (F .F-hom f) (F .F-hom g) h
      (F .F-hom fg) (F .F-seq f g fg efg)
      gh egh k e₁ e₂ fᴰ gᴰ hᴰ
  reindexSPshᶠᴰ .⋆ᴰ-coh f g h h' e e' q fᴰ gᴰ =
    Qᴰ .⋆ᴰ-coh (F .F-hom f) g h h' e e' q fᴰ gᴰ
  reindexSPshᶠᴰ .isSetPshᴰ = Qᴰ .isSetPshᴰ

-- ------------------------------------------------------------------
-- EVERY displayed presheaf is a forded one.  This is what makes the
-- above more than a definition: the existing library of `Presheafᴰ`
-- instances plugs in.  The reindexing is `Eq.transport`, exactly as
-- `fromCategoryᴰ` now uses, so the lifted action COMPUTES at the
-- identity ford (see `fromPresheafᴰ-⋆-computes`).
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module P = PresheafNotation P
    module Cᴰ = Categoryᴰ Cᴰ
    module R = Reasoning Cᴰ
    module Pᴰ = PresheafᴰNotation Pᴰ

    -- the base's Eq-reind, definitionally the one `fromCategoryᴰ` uses
    reindE : {x y : C.ob} {f g : C [ x , y ]}
      {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      → f Eq.≡ g → Cᴰ.Hom[ f ][ xᴰ , yᴰ ] → Cᴰ.Hom[ g ][ xᴰ , yᴰ ]
    reindE p fᴰ = Eq.transport (λ h → Cᴰ.Hom[ h ][ _ , _ ]) p fᴰ

    reindE-filler : {x y : C.ob} {f g : C [ x , y ]}
      {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      (p : f Eq.≡ g) (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
      → Path (Σ[ h ∈ C [ x , y ] ] Cᴰ.Hom[ h ][ xᴰ , yᴰ ])
          (f , fᴰ) (g , reindE p fᴰ)
    reindE-filler Eq.refl fᴰ = refl

    -- the presheaf's Eq-reind
    reindEP : {x : C.ob} {g h : P.p[ x ]} {xᴰ : Cᴰ.ob[ x ]}
      → g Eq.≡ h → Pᴰ.p[ g ][ xᴰ ] → Pᴰ.p[ h ][ xᴰ ]
    reindEP p gᴰ = Eq.transport (λ q → Pᴰ.p[ q ][ _ ]) p gᴰ

    reindEP-filler : {x : C.ob} {g h : P.p[ x ]} {xᴰ : Cᴰ.ob[ x ]}
      (p : g Eq.≡ h) (gᴰ : Pᴰ.p[ g ][ xᴰ ])
      → Path (Σ[ q ∈ P.p[ x ] ] Pᴰ.p[ q ][ xᴰ ])
          (g , gᴰ) (h , reindEP p gᴰ)
    reindEP-filler Eq.refl gᴰ = refl

  open Presheafᶠᴰ

  fromPresheafᴰ : Presheafᶠᴰ P (fromCategoryᴰ Cᴰ) ℓPᴰ
  fromPresheafᴰ .p[_][_] = Pᴰ.p[_][_]
  fromPresheafᴰ .⋆ᴰ f g h e fᴰ gᴰ = reindEP e (fᴰ Pᴰ.⋆ᴰ gᴰ)
  fromPresheafᴰ .⋆IdLᴰ i ei g e gᴰ = Pᴰ.rectify $ Pᴰ.≡out $
      sym (reindEP-filler e _)
    ∙ Pᴰ.⟨ sym (reindE-filler ei Cᴰ.idᴰ) ⟩⋆⟨ refl ⟩
    ∙ Pᴰ.⋆IdL _
  fromPresheafᴰ .⋆Assocᴰ f g h fg efg gh egh k e₁ e₂ fᴰ gᴰ hᴰ =
    Pᴰ.rectify $ Pᴰ.≡out $
      sym (reindEP-filler e₁ _)
    ∙ Pᴰ.⟨ sym (reindE-filler efg _) ⟩⋆⟨ refl ⟩
    ∙ Pᴰ.⋆Assoc _ _ _
    ∙ Pᴰ.⟨ refl ⟩⋆⟨ reindEP-filler egh _ ⟩
    ∙ reindEP-filler e₂ _
  fromPresheafᴰ .⋆ᴰ-coh f g h h' e e' q fᴰ gᴰ = Pᴰ.rectify $ Pᴰ.≡out $
    sym (reindEP-filler e _) ∙ reindEP-filler e' _
  fromPresheafᴰ .isSetPshᴰ = Pᴰ.isSetPshᴰ

  -- THE PAYOFF OF THE Eq FORD.  `Eq.transport C Eq.refl b = b`, so the
  -- lifted action COMPUTES wherever the ford is `Eq.refl` --- which is
  -- every place `∫Pᶠ` uses it.  Under the earlier Path-valued ford
  -- this FAILED, because `subst B refl b` is stuck for neutral `B`.
  fromPresheafᴰ-⋆-computes : {x y : C.ob}
    {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
    {f : C [ x , y ]} {g : P.p[ y ]}
    (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Pᴰ.p[ g ][ yᴰ ])
    → fromPresheafᴰ .⋆ᴰ f g _ Eq.refl fᴰ gᴰ ≡ (fᴰ Pᴰ.⋆ᴰ gᴰ)
  fromPresheafᴰ-⋆-computes fᴰ gᴰ = refl

-- ------------------------------------------------------------------
-- THE MEASUREMENT.  The total presheaf of the forded displayed
-- representable is the representable of the total category ON THE
-- NOSE.
--
-- Compare Displayed.Presheaf.Properties.TotalCatYoPshIso, which can
-- only produce a `PshIso (∫P (Cᴰ [-][-, cᴰ ])) ((∫C Cᴰ) [-, c , cᴰ ])`
-- --- and produces it via `eqToPshIso _ Eq.refl Eq.refl`, i.e. by
-- observing that the two agree on `F-ob` and `F-hom` and routing
-- around `F-id`/`F-seq` through `Cubical.Data.Equality`.  Here they
-- agree on `F-id` and `F-seq` too, so there is nothing to route
-- around.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ')
  {c : Category.ob C} (cᴰ : Categoryᶠᴰ.ob[ Cᴰ ] c) where
  private
    LHS = ∫Pᶠ (_[-][-,_]ᶠ Cᴰ cᴰ)
    RHS = (∫ᶠ Cᴰ) [-, (c , cᴰ) ]
  open Functor

  test-ob : LHS .F-ob ≡ RHS .F-ob
  test-ob = refl

  test-hom : (λ {x y} → LHS .F-hom {x} {y}) ≡ (λ {x y} → RHS .F-hom {x} {y})
  test-hom = refl

  test-id : (λ {x} → LHS .F-id {x}) ≡ (λ {x} → RHS .F-id {x})
  test-id = refl

  test-seq : (λ {x y z} → LHS .F-seq {x} {y} {z})
           ≡ (λ {x y z} → RHS .F-seq {x} {y} {z})
  test-seq = refl

  -- ...so the identity itself holds, and its proof does not transport
  -- anything: every component is constant along the interval.  The
  -- only thing standing between this and `refl` is that `Functor` is
  -- declared `no-eta-equality` upstream.
  ∫Pᶠ-yo : LHS ≡ RHS
  ∫Pᶠ-yo i .F-ob = LHS .F-ob
  ∫Pᶠ-yo i .F-hom = LHS .F-hom
  ∫Pᶠ-yo i .F-id = LHS .F-id
  ∫Pᶠ-yo i .F-seq = LHS .F-seq

  -- In particular it IS represented, and the witness is literally the
  -- base category's.  A `UniversalElement` only mentions `F-ob` and
  -- `F-hom`, so `selfUnivElt` typechecks at this type on the nose ---
  -- no bespoke universal-property record, and no transport.
  ∫Pᶠ-yo-ue : UniversalElement (∫ᶠ Cᴰ) LHS
  ∫Pᶠ-yo-ue .UniversalElement.vertex =
    selfUnivElt (∫ᶠ Cᴰ) (c , cᴰ) .UniversalElement.vertex
  ∫Pᶠ-yo-ue .UniversalElement.element =
    selfUnivElt (∫ᶠ Cᴰ) (c , cᴰ) .UniversalElement.element
  ∫Pᶠ-yo-ue .UniversalElement.universal =
    selfUnivElt (∫ᶠ Cᴰ) (c , cᴰ) .UniversalElement.universal

-- ...and the vertical action of the forded displayed representable IS
-- vertical composition in `Cᴰ`, on the nose.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᶠᴰ C ℓᴰ ℓᴰ')
  {c : Category.ob C} (cᴰ : Categoryᶠᴰ.ob[ Cᴰ ] c) where
  private
    module C = Category C
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module R = PresheafᶠᴰNotation (_[-][-,_]ᶠ Cᴰ cᴰ)

  ⋆ⱽᴰ-is-⋆ⱽᴰ' : {x : C.ob} {xᴰ xᴰ' : Cᴰ.ob[ x ]} {g : C [ x , c ]}
    (fⱽ : R.vᴰ[ xᴰ , xᴰ' ]) (gᴰ : Cᴰ.Hom[ g ][ xᴰ' , cᴰ ])
    → (fⱽ R.⋆ⱽᴰ gᴰ) ≡ (fⱽ R.⋆ⱽᴰ' gᴰ)
  ⋆ⱽᴰ-is-⋆ⱽᴰ' fⱽ gᴰ = refl

-- ------------------------------------------------------------------
-- THE TWO NEGATIVE CONTROLS, exhibited rather than asserted.  Both
-- were re-checked against the re-oriented Eq-forded core; both still
-- fail, and the error messages say why.
--
-- (A) The Eq ford on `PshHomᶠ` is not optional.  Reindexing along the
--     stock Path-forded `PshHomStrict` inserts
--     `Eq.pathToEq ∘ Eq.eqToPath`, which is not the identity, so
--     strict functoriality is lost even for `idPshHomStrict`:
--
--       scratchA : reindᶠ (fromPshHomStrict idPshHomStrict) Pᴰ ≡ Pᴰ
--       scratchA = refl
--
--     rejects with a stuck `Agda.Builtin.Equality.transpX-_≡_ …`
--     against the bare ford variable.  Contrast `reindᶠ-Id` above,
--     which is `refl`.
--
-- (B) Reindexing the BASE presheaf along a `StrictFunctor` is still
--     not strict, and `Strict→Fun`'s move to
--     `Eq.eqToPath (Eq.sym …)` does not change that.  Re-measured
--     componentwise:
--
--       (Q ∘F (Strict→Fun SId ^opF)) .F-ob  ≡ Q .F-ob   -- refl  OK
--       (Q ∘F (Strict→Fun SId ^opF)) .F-hom ≡ Q .F-hom  -- refl  OK
--       (Q ∘F (Strict→Fun SId ^opF)) .F-id  ≡ Q .F-id   -- REJECTED
--
--     The rejection is a `hcomp`/`doubleComp-faces` blob: the culprit
--     is `_∘F_`, which builds its `F-id` with `_∙∙_` regardless of how
--     nice the two factors are.  So the fix is not on the ford side at
--     all --- it is to ford `Presheaf` itself, giving `⋆IdL`/`⋆Assoc`
--     Eq witnesses so that nothing is composed.

-- (C) ...and the Eq ford is what makes `fromPresheafᴰ-⋆-computes`
--     possible.  The Path-forded predecessor reindexed with
--     `hSetReasoning.reind`, which is declared `opaque` upstream, so
--     even at `refl` it is stuck:
--
--       scratchC : Pᴰ.reind refl (fᴰ Pᴰ.⋆ᴰ gᴰ) ≡ (fᴰ Pᴰ.⋆ᴰ gᴰ)
--       scratchC = refl
--
--     rejects with `depReasoning.reind Pᴰ.p[_][ xᴰ ] refl (fᴰ ⋆ᴰ gᴰ)`
--     against the bare composite.  `Eq.transport _ Eq.refl b = b` is a
--     defining clause, so the Eq version needs no unfolding pragma.
