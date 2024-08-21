{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Section.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq
import      Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Equality
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

  -- Section without a qualifier means *local* section.
  record Section : Type (ℓ-max (ℓ-max ℓC ℓC')
                        (ℓ-max (ℓ-max ℓD ℓD')
                        (ℓ-max ℓCᴰ ℓCᴰ')))
    where
    field
      F-obᴰ  : ∀ d → Cᴰ.ob[ F ⟅ d ⟆ ]
      F-homᴰ : ∀ {d d'} (f : D.Hom[ d , d' ])
        → Cᴰ.Hom[ F ⟪ f ⟫ ][ F-obᴰ d , F-obᴰ d' ]
      F-idᴰ : ∀ {d} → F-homᴰ (D.id {d}) Cᴰ.≡[ F .F-id ] Cᴰ.idᴰ
      F-seqᴰ : ∀ {d d' d''}
            → (f : D.Hom[ d , d' ])(g : D.Hom[ d' , d'' ])
            → F-homᴰ (f D.⋆ g) Cᴰ.≡[ F .F-seq f g ] F-homᴰ f Cᴰ.⋆ᴰ F-homᴰ g
