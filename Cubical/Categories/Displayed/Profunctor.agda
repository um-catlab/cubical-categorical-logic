{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Profunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Data.Sigma

open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Functors.More
import Cubical.Categories.Constructions.TotalCategory as TotalCat

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level
    ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓSᴰ : Level

open Category
open Functor

-- A profunctor, also called a distributor is a generalization of a
-- functor where the values are not objects of the codomain, but
-- instead presheaves
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
    → UniversalElementᴰ _ (Rᴰ.F-obᴰ xᴰ) (ues x)

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
  ∫UEs : ∀ {ues : UniversalElements R} → (uesᴰ : UniversalElementsᴰ ues Rᴰ)
    → UniversalElements ∫Prof
  ∫UEs uesᴰ (x , xᴰ) = ∫UE _ _ (uesᴰ x xᴰ)
