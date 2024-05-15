{-
  Displayed limits, aka lifted limits.
-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.AsRepresentable
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Adjoint.More
-- TODO: fix this naming to be Functors
open import Cubical.Categories.Displayed.Instances.Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓJ ℓJ' ℓJᴰ ℓJᴰ' : Level

open Functor
open Functorᴰ
open NatTrans
open NatTransᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {J : Category ℓJ ℓJ'} {Jᴰ : Categoryᴰ J ℓJᴰ ℓJᴰ'}
       where
  private
    import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
    module R = HomᴰReasoning Cᴰ
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
  ΔFᴰ : Functorᴰ ΔF Cᴰ (FUNCTORᴰ Jᴰ Cᴰ)
  ΔFᴰ .F-obᴰ c .F-obᴰ _ = c
  ΔFᴰ .F-obᴰ c .F-homᴰ _ = Cᴰ.idᴰ
  ΔFᴰ .F-obᴰ c .F-idᴰ = refl
  ΔFᴰ .F-obᴰ c .F-seqᴰ _ _ = R.≡[]-rectify (symP (Cᴰ.⋆IdLᴰ _))
  ΔFᴰ .F-homᴰ fᴰ .N-obᴰ _ = fᴰ
  ΔFᴰ .F-homᴰ fᴰ .N-homᴰ _ = R.≡[]-rectify (R.≡[]∙ (C.⋆IdL _) (sym (C.⋆IdR _))
    (Cᴰ.⋆IdLᴰ _)
    (symP (Cᴰ.⋆IdRᴰ _)))
  ΔFᴰ .F-idᴰ = makeNatTransPathᴰ _ _ _ refl
  ΔFᴰ .F-seqᴰ fᴰ gᴰ = makeNatTransPathᴰ _ _ _ refl

  limitᴰ : {F : Functor J C} → RightAdjointAt ΔF F → Functorᴰ F Jᴰ Cᴰ → Type _
  limitᴰ = RightAdjointAtᴰ ΔFᴰ

limitsᴰOfShape :
  {C : Category ℓC ℓC'} {J : Category ℓJ ℓJ'}
  → limitsOfShape C J
  → Categoryᴰ C ℓCᴰ ℓCᴰ'
  → Categoryᴰ J ℓJᴰ ℓJᴰ'
  → Type _
limitsᴰOfShape lims Cᴰ Jᴰ = RightAdjointᴰ (ΔFᴰ {Cᴰ = Cᴰ}{Jᴰ = Jᴰ}) lims

liftsLimitsᴰOfShape :
  {C : Category ℓC ℓC'}
  {J : Category ℓJ ℓJ'}
  → limitsOfShape C J
  → Categoryᴰ C ℓCᴰ ℓCᴰ'
  → Type _
liftsLimitsᴰOfShape lims Cᴰ = limitsᴰOfShape lims Cᴰ (Unitᴰ _)

liftsLimits : {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → ∀ (ℓJ ℓJ' : Level) → Type _
liftsLimits {C = C} Cᴰ ℓJ ℓJ' =
  ∀ (J : Category ℓJ ℓJ')
  → (limitOfJ : ∀ (D : Functor J C) → limit D)
  → ∀ {D : Functor J C} (Dᴰ : Functorᴰ D (Unitᴰ _) Cᴰ)
  → limitᴰ (limitOfJ D) Dᴰ
