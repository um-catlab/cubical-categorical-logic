{-
   Local Sections of a displayed category
          A
        ↗ |
       /  |
    M /   |
     /    |
    /     ↓
   Δ ---→ Γ
       γ
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Section.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Categoryᴰ
open Functor

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (F : Functor D C)
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         where
  private
    module C = Category C
    module D = Category D
    module Cᴰ = Categoryᴰ Cᴰ
    module F = Functor F

  -- This is a *Local* Section. If F is Id then this is a *Global* section.
  record Section : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓD ℓD') (ℓ-max ℓCᴰ ℓCᴰ'))) where
    field
      F-obᴰ  : ∀ d → Cᴰ.ob[ F ⟅ d ⟆ ]
      F-homᴰ : ∀ {d d'} (f : D.Hom[ d , d' ])
        → Cᴰ.Hom[ F ⟪ f ⟫ ][ F-obᴰ d , F-obᴰ d' ]
      F-idᴰ : ∀ {d} → F-homᴰ (D.id {d}) Cᴰ.≡[ F .F-id ] Cᴰ.idᴰ
      F-seqᴰ : ∀ {d d' d''}
            → (f : D.Hom[ d , d' ])(g : D.Hom[ d' , d'' ])
            → F-homᴰ (f D.⋆ g) Cᴰ.≡[ F .F-seq f g ] F-homᴰ f Cᴰ.⋆ᴰ F-homᴰ g

module _ {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F : Functor C D}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Functor
  open Section
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module R = HomᴰReasoning Dᴰ
  compSectionFunctor : Section F Dᴰ → (G : Functor B C) → Section (F ∘F G) Dᴰ
  compSectionFunctor Fᴰ G .F-obᴰ d     = Fᴰ .F-obᴰ (G .F-ob d)
  compSectionFunctor Fᴰ G .F-homᴰ f    = Fᴰ .F-homᴰ (G .F-hom f)
  compSectionFunctor Fᴰ G .F-idᴰ       = R.≡[]-rectify (R.≡[]∙ _ _
    (cong (Fᴰ .F-homᴰ) (G .F-id))
    (Fᴰ .F-idᴰ))
  compSectionFunctor Fᴰ G .F-seqᴰ f g = R.≡[]-rectify (R.≡[]∙ _ _
    (cong (Fᴰ .F-homᴰ) (G .F-seq f g))
    (Fᴰ .F-seqᴰ (G .F-hom f) (G .F-hom g)))

module _ {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F : Functor C D}
         {G : Functor B C}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Functor
  open Functorᴰ
  open Section
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Dᴰ
  compFunctorᴰSection : Functorᴰ F Cᴰ Dᴰ → Section G Cᴰ → Section (F ∘F G) Dᴰ
  compFunctorᴰSection Fᴰ Gᴰ .F-obᴰ d    = Fᴰ .F-obᴰ (Gᴰ .F-obᴰ d)
  compFunctorᴰSection Fᴰ Gᴰ .F-homᴰ f   = Fᴰ .F-homᴰ (Gᴰ .F-homᴰ f)
  compFunctorᴰSection Fᴰ Gᴰ .F-idᴰ      = R.≡[]-rectify (R.≡[]∙ _ _
    (λ i → Fᴰ .F-homᴰ (Gᴰ .F-idᴰ i))
    (Fᴰ .F-idᴰ))
  compFunctorᴰSection Fᴰ Gᴰ .F-seqᴰ f g = R.≡[]-rectify (R.≡[]∙ _ _
    (λ i → Fᴰ .F-homᴰ (Gᴰ .F-seqᴰ f g i))
    (Fᴰ .F-seqᴰ (Gᴰ .F-homᴰ f) (Gᴰ .F-homᴰ g)))

