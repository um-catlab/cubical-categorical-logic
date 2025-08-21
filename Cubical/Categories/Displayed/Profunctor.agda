{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Profunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level
    ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓSᴰ : Level

Profunctorᴰ : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  → Profunctor C D ℓS
  → (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  → ∀ ℓSᴰ → Type _
Profunctorᴰ P Cᴰ Dᴰ ℓSᴰ = Functorᴰ P Cᴰ (PRESHEAFᴰ Dᴰ _ ℓSᴰ)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
         ℓS ℓSᴰ where
  PROFUNCTORᴰ : Categoryᴰ (PROFUNCTOR C D ℓS) _ _
  PROFUNCTORᴰ = FUNCTORᴰ Cᴰ (PRESHEAFᴰ Dᴰ ℓS ℓSᴰ)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {R : Profunctor C D ℓS}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (ues : UniversalElements R)
         (Rᴰ : Profunctorᴰ R Cᴰ Dᴰ ℓSᴰ)
         where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Rᴰ = Functorᴰ Rᴰ
  UniversalElementsᴰ : Type _
  UniversalElementsᴰ = ∀ x (xᴰ : Cᴰ.ob[ x ])
    → UniversalElementᴰ _ (ues x) (Rᴰ.F-obᴰ xᴰ)

-- A vertical profunctor is a profunctor over Yoneda
Profunctorⱽ : {C : Category ℓC ℓC'}
  → (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → (Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ')
  → ∀ ℓSᴰ → Type _
Profunctorⱽ Cᴰ Dᴰ ℓSᴰ = Profunctorᴰ YO Cᴰ Dᴰ ℓSᴰ

module _ {C : Category ℓC ℓC'}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
         (Rᴰ : Profunctorⱽ Cᴰ Dᴰ ℓSᴰ)
         where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Rᴰ = Functorᴰ Rᴰ
  UniversalElementsⱽ : Type _
  UniversalElementsⱽ = ∀ x (xᴰ : Cᴰ.ob[ x ]) →
    UniversalElementⱽ Dᴰ x (Rᴰ.F-obᴰ xᴰ)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {R : Profunctor C D ℓS}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (Rᴰ : Profunctorᴰ R Cᴰ Dᴰ ℓSᴰ)
         where
  ∫Prof : Profunctor (TotalCat.∫C Cᴰ) (TotalCat.∫C Dᴰ) (ℓ-max ℓS ℓSᴰ)
  ∫Prof = ((postcomposeF _ ΣF) ∘F ∫F-Functor (Dᴰ ^opᴰ) (SETᴰ ℓS ℓSᴰ))
    ∘F TotalCat.∫F Rᴰ

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Rᴰ = Functorᴰ Rᴰ
  open UniversalElement
  open UniversalElementᴰ
  ∫ues : ∀ {ues : UniversalElements R} → (uesᴰ : UniversalElementsᴰ ues Rᴰ)
    → UniversalElements ∫Prof
  ∫ues uesᴰ (x , xᴰ) = ∫ue (uesᴰ x xᴰ)
