{-# OPTIONS --safe #-}

module Cubical.Categories.Adjoint.UniversalElements where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category

RightAdjoint : (C : Category ℓC ℓC')
               (D : Category ℓD ℓD')
               (F : Functor C D) → Type _
RightAdjoint C D F  = UniversalElements D C (Functor→Profo-* C D F)

RightAdjointAt : (C : Category ℓC ℓC')
                 (D : Category ℓD ℓD')
                 (F : Functor C D)
                 (d : D .ob) → Type _
RightAdjointAt C D F = UniversalElementAt D C (Functor→Profo-* C D F)

-- Uh Oh
RightAdjointAt' : (C : Category ℓC ℓC')
                  (D : Category ℓD ℓD')
                  (F : Functor C D) (d : D .ob)
                → Type _
RightAdjointAt' C D F d  =
  UniversalElement C ((D [-, d ]) ∘F (F ^opF))

RightAdjointAt→Prime : (C : Category ℓC ℓC')
                 (D : Category ℓD ℓD')
                 (F : Functor C D)
                 (d : D .ob)
                 → RightAdjointAt C D F d → RightAdjointAt' C D F d
RightAdjointAt→Prime C D F d x .UniversalElement.vertex =
  UniversalElement.vertex x
RightAdjointAt→Prime C D F d x .UniversalElement.element =
  UniversalElement.element x
RightAdjointAt→Prime C D F d x .UniversalElement.universal =
  UniversalElement.universal x

RightAdjoint' : (C : Category ℓC ℓC')
                (D : Category ℓD ℓD')
                (F : Functor C D)
              → Type _
RightAdjoint' C D F = ∀ d → RightAdjointAt' C D F d

IdRightAdj' : (C : Category ℓC ℓC')
      → RightAdjoint' C C Id
IdRightAdj' C c .UniversalElement.vertex = c
IdRightAdj' C c .UniversalElement.element = id C
IdRightAdj' C c .UniversalElement.universal c' =
  isoToIsEquiv (iso _ (λ z → z) (C .⋆IdR) (C .⋆IdR))

LeftAdjoint : (C : Category ℓC ℓC')
              (D : Category ℓD ℓD')
              (F : Functor C D) → Type _
LeftAdjoint C D F  = RightAdjoint (C ^op) (D ^op) (F ^opF)

LeftAdjointAt : (C : Category ℓC ℓC')
                (D : Category ℓD ℓD')
                (F : Functor C D)
                (d : D .ob) → Type _
LeftAdjointAt C D F = RightAdjointAt (C ^op) (D ^op) (F ^opF)
