{-# OPTIONS --safe #-}

module Cubical.Categories.Adjoint.UniversalElements where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category

RightAdjoint : (C : Category ℓC ℓC')
               (D : Category ℓD ℓD')
               (F : Functor C D) → Type _
RightAdjoint C D F  = ParamUnivElt D C (Functor→Profo-* C D F)

RightAdjointAt : (C : Category ℓC ℓC')
                 (D : Category ℓD ℓD')
                 (F : Functor C D)
                 (d : D .ob) → Type _
RightAdjointAt C D F = RepresentableAt D C (Functor→Profo-* C D F)

LeftAdjoint : (C : Category ℓC ℓC')
              (D : Category ℓD ℓD')
              (F : Functor C D) → Type _
LeftAdjoint C D F  = RightAdjoint (C ^op) (D ^op) (F ^opF)

LeftAdjointAt : (C : Category ℓC ℓC')
                (D : Category ℓD ℓD')
                (F : Functor C D)
                (d : D .ob) → Type _
LeftAdjointAt C D F = RightAdjointAt (C ^op) (D ^op) (F ^opF)
