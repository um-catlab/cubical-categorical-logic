{-# OPTIONS --lossy-unification #-}
{-

  FORDED DISPLAYED FUNCTORS.

  The primitive notion is the VERTICAL one: a map of forded displayed
  categories over the SAME base.  Both of its laws are ordinary
  equations, and both are forded on the INPUT side exactly the way
  `StrictFunctor`'s are --- the field takes any `iᴰ` together with a
  witness `idᴰ ≡ iᴰ`.  Following Functors.Strict.Base, the ford on the
  BASE hom is `Eq`-valued and oriented FORWARDS, and the conclusion is
  oriented the same way (`idᴰ ≡ F-homⱽ iᴰ`, not the reverse), so that
  `_Vᶠ∘_` and `reindexSⱽ` hand the witness over verbatim --- no `sym`
  anywhere.  That is what makes vertical composition definitionally
  unital and associative for VARIABLES.

  A displayed functor over a strict `F` is then not a new record but a
  vertical functor into the reindexing:

      Functorᶠᴰ F Cᴰ Dᴰ  =  Functorⱽᶠ Cᴰ (reindexS F Dᴰ)

  by DEFINITION.  Because `reindexS` is strictly functorial (Forded.agda)
  this makes composition of displayed functors land on the nose:
  `Functorᶠᴰ F Cᴰ (reindexS G Eᴰ)` and `Functorᶠᴰ (G S∘ F) Cᴰ Eᴰ` are the
  same type, so `_∘ᶠᴰ_` needs no coercion, and its unit and associativity
  laws hold by `refl`.

-}
module Cubical.Categories.Displayed.Forded.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functors.Strict.Base
open import Cubical.Categories.Displayed.Forded

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

open StrictFunctor

-- ------------------------------------------------------------------
-- VERTICAL forded displayed functors.
module _ {C : Category ℓC ℓC'}
  (Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ') (Dᴰ : Categoryᶠᴰ C ℓDᴰ ℓDᴰ') where
  private
    module C = Category C
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module Dᴰ = Categoryᶠᴰ Dᴰ

  record Functorⱽᶠ : Type (ℓ-max (ℓ-max ℓC ℓC')
                          (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') (ℓ-max ℓDᴰ ℓDᴰ'))) where
    field
      F-obⱽ : {x : C.ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ x ]
      F-homⱽ : {x y : C.ob} {f : C [ x , y ]}
        {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
        → Cᴰ.Hom[ f ][ xᴰ , yᴰ ]
        → Dᴰ.Hom[ f ][ F-obⱽ xᴰ , F-obⱽ yᴰ ]

      -- forded on the input, like StrictFunctor's F-id, and oriented
      -- the same way it is
      F-idⱽ : {x : C.ob} {xᴰ : Cᴰ.ob[ x ]}
        (i : C [ x , x ]) (ei : C.id Eq.≡ i)
        (iᴰ : Cᴰ.Hom[ i ][ xᴰ , xᴰ ])
        → Cᴰ.idᴰ i ei ≡ iᴰ
        → Dᴰ.idᴰ i ei ≡ F-homⱽ iᴰ

      F-seqⱽ : {x y z : C.ob}
        {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
        (f : C [ x , y ]) (g : C [ y , z ]) (h : C [ x , z ])
        (e : f C.⋆ g Eq.≡ h)
        (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ.Hom[ g ][ yᴰ , zᴰ ])
        (hᴰ : Cᴰ.Hom[ h ][ xᴰ , zᴰ ])
        → Cᴰ.⋆ᴰ f g h e fᴰ gᴰ ≡ hᴰ
        → Dᴰ.⋆ᴰ f g h e (F-homⱽ fᴰ) (F-homⱽ gᴰ) ≡ F-homⱽ hᴰ

open Functorⱽᶠ

-- ------------------------------------------------------------------
-- A displayed functor over F is a vertical functor into the
-- reindexing.  This is a DEFINITION, not a transported equivalence.
Functorᶠᴰ : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  → StrictFunctor C D
  → Categoryᶠᴰ C ℓCᴰ ℓCᴰ' → Categoryᶠᴰ D ℓDᴰ ℓDᴰ'
  → Type _
Functorᶠᴰ F Cᴰ Dᴰ = Functorⱽᶠ Cᴰ (reindexS F Dᴰ)

-- ------------------------------------------------------------------
-- IDENTITY and VERTICAL COMPOSITION.  Nothing is built, so the laws
-- pass the ford along instead of building a `_∙_` chain.
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ'} where
  Idⱽᶠ : Functorⱽᶠ Cᴰ Cᴰ
  Idⱽᶠ .F-obⱽ  = λ z → z
  Idⱽᶠ .F-homⱽ = λ z → z
  Idⱽᶠ .F-idⱽ  i ei iᴰ e = e
  Idⱽᶠ .F-seqⱽ f g h e fᴰ gᴰ hᴰ eᴰ = eᴰ

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᶠᴰ C ℓDᴰ ℓDᴰ'}
  {Eᴰ : Categoryᶠᴰ C ℓEᴰ ℓEᴰ'} where

  _Vᶠ∘_ : Functorⱽᶠ Dᴰ Eᴰ → Functorⱽᶠ Cᴰ Dᴰ → Functorⱽᶠ Cᴰ Eᴰ
  (G Vᶠ∘ F) .F-obⱽ  = λ z → G .F-obⱽ (F .F-obⱽ z)
  (G Vᶠ∘ F) .F-homⱽ = λ z → G .F-homⱽ (F .F-homⱽ z)
  (G Vᶠ∘ F) .F-idⱽ i ei iᴰ e =
    G .F-idⱽ i ei (F .F-homⱽ iᴰ) (F .F-idⱽ i ei iᴰ e)
  (G Vᶠ∘ F) .F-seqⱽ f g h e fᴰ gᴰ hᴰ eᴰ =
    G .F-seqⱽ f g h e (F .F-homⱽ fᴰ) (F .F-homⱽ gᴰ) (F .F-homⱽ hᴰ)
      (F .F-seqⱽ f g h e fᴰ gᴰ hᴰ eᴰ)

-- the laws, for VARIABLES
module _ {C : Category ℓC ℓC'}
  (Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ') (Dᴰ : Categoryᶠᴰ C ℓDᴰ ℓDᴰ') where
  Vᶠ∘-lUnit : (F : Functorⱽᶠ Cᴰ Dᴰ) → (Idⱽᶠ Vᶠ∘ F) ≡ F
  Vᶠ∘-lUnit F = refl

  Vᶠ∘-rUnit : (F : Functorⱽᶠ Cᴰ Dᴰ) → (F Vᶠ∘ Idⱽᶠ) ≡ F
  Vᶠ∘-rUnit F = refl

module _ {C : Category ℓC ℓC'}
  {Aᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ'} {Bᴰ : Categoryᶠᴰ C ℓDᴰ ℓDᴰ'}
  {Cᴰ : Categoryᶠᴰ C ℓEᴰ ℓEᴰ'} {Dᴰ : Categoryᶠᴰ C ℓCᴰ ℓEᴰ'} where
  Vᶠ∘-Assoc : (F : Functorⱽᶠ Aᴰ Bᴰ) (G : Functorⱽᶠ Bᴰ Cᴰ)
              (H : Functorⱽᶠ Cᴰ Dᴰ)
    → ((H Vᶠ∘ G) Vᶠ∘ F) ≡ (H Vᶠ∘ (G Vᶠ∘ F))
  Vᶠ∘-Assoc F G H = refl

-- ------------------------------------------------------------------
-- WHISKERING a vertical functor along a reindexing.  Again no
-- transport and no `sym`: the reindexed ford is handed straight to the
-- original law.
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : StrictFunctor C D)
  {Cᴰ : Categoryᶠᴰ D ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᶠᴰ D ℓDᴰ ℓDᴰ'} where

  reindexSⱽ : Functorⱽᶠ Cᴰ Dᴰ
            → Functorⱽᶠ (reindexS F Cᴰ) (reindexS F Dᴰ)
  reindexSⱽ G .F-obⱽ  = G .F-obⱽ
  reindexSⱽ G .F-homⱽ = G .F-homⱽ
  reindexSⱽ G .F-idⱽ i ei iᴰ e =
    G .F-idⱽ (F .F-hom i) (F .F-id i ei) iᴰ e
  reindexSⱽ G .F-seqⱽ f g h e fᴰ gᴰ hᴰ eᴰ =
    G .F-seqⱽ (F .F-hom f) (F .F-hom g) (F .F-hom h)
      (F .F-seq f g h e) fᴰ gᴰ hᴰ eᴰ

-- whiskering is strictly functorial, for variables
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : StrictFunctor C D) (Cᴰ : Categoryᶠᴰ D ℓCᴰ ℓCᴰ') where
  reindexSⱽ-Id : reindexSⱽ F {Cᴰ}{Cᴰ} Idⱽᶠ ≡ Idⱽᶠ
  reindexSⱽ-Id = refl

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : StrictFunctor C D)
  {Cᴰ : Categoryᶠᴰ D ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᶠᴰ D ℓDᴰ ℓDᴰ'}
  {Eᴰ : Categoryᶠᴰ D ℓEᴰ ℓEᴰ'} where
  reindexSⱽ-comp : (G : Functorⱽᶠ Dᴰ Eᴰ) (H : Functorⱽᶠ Cᴰ Dᴰ)
    → reindexSⱽ F (G Vᶠ∘ H) ≡ (reindexSⱽ F G Vᶠ∘ reindexSⱽ F H)
  reindexSⱽ-comp G H = refl

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  (F : StrictFunctor C D) (G : StrictFunctor D E)
  {Eᴰ : Categoryᶠᴰ E ℓEᴰ ℓEᴰ'} {Eᴰ' : Categoryᶠᴰ E ℓCᴰ ℓCᴰ'} where
  -- reindexing a whiskering is whiskering along the composite
  reindexSⱽ-S∘ : (H : Functorⱽᶠ Eᴰ Eᴰ')
    → reindexSⱽ F (reindexSⱽ G H) ≡ reindexSⱽ (G S∘ F) H
  reindexSⱽ-S∘ H = refl

-- ------------------------------------------------------------------
-- COMPOSITION OF DISPLAYED FUNCTORS.  The types line up ON THE NOSE
-- because `reindexS (G S∘ F) Eᴰ` and `reindexS F (reindexS G Eᴰ)` are
-- definitionally equal.
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  {F : StrictFunctor C D} {G : StrictFunctor D E}
  {Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᶠᴰ D ℓDᴰ ℓDᴰ'}
  {Eᴰ : Categoryᶠᴰ E ℓEᴰ ℓEᴰ'} where

  _∘ᶠᴰ_ : Functorᶠᴰ G Dᴰ Eᴰ → Functorᶠᴰ F Cᴰ Dᴰ → Functorᶠᴰ (G S∘ F) Cᴰ Eᴰ
  Gᴰ ∘ᶠᴰ Fᴰ = reindexSⱽ F Gᴰ Vᶠ∘ Fᴰ

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : StrictFunctor C D}
  {Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᶠᴰ D ℓDᴰ ℓDᴰ'} where

  -- `Idⱽᶠ : Functorᶠᴰ SId Cᴰ Cᴰ` --- SId's reindexing IS the identity
  ∘ᶠᴰ-lUnit : (Fᴰ : Functorᶠᴰ F Cᴰ Dᴰ) → (Idⱽᶠ ∘ᶠᴰ Fᴰ) ≡ Fᴰ
  ∘ᶠᴰ-lUnit Fᴰ = refl

  ∘ᶠᴰ-rUnit : (Fᴰ : Functorᶠᴰ F Cᴰ Dᴰ) → (Fᴰ ∘ᶠᴰ Idⱽᶠ) ≡ Fᴰ
  ∘ᶠᴰ-rUnit Fᴰ = refl

module _ {ℓB ℓB' ℓBᴰ ℓBᴰ' : Level}
  {B : Category ℓB ℓB'} {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  {F : StrictFunctor B C} {G : StrictFunctor C D} {H : StrictFunctor D E}
  {Bᴰ : Categoryᶠᴰ B ℓBᴰ ℓBᴰ'} {Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ'}
  {Dᴰ : Categoryᶠᴰ D ℓDᴰ ℓDᴰ'} {Eᴰ : Categoryᶠᴰ E ℓEᴰ ℓEᴰ'} where

  ∘ᶠᴰ-Assoc : (Fᴰ : Functorᶠᴰ F Bᴰ Cᴰ) (Gᴰ : Functorᶠᴰ G Cᴰ Dᴰ)
              (Hᴰ : Functorᶠᴰ H Dᴰ Eᴰ)
    → ((Hᴰ ∘ᶠᴰ Gᴰ) ∘ᶠᴰ Fᴰ) ≡ (Hᴰ ∘ᶠᴰ (Gᴰ ∘ᶠᴰ Fᴰ))
  ∘ᶠᴰ-Assoc Fᴰ Gᴰ Hᴰ = refl
