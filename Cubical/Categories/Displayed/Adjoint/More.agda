{-
  Definition of an adjoint pair displayed over another adjoint pair
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Adjoint.More where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Presheaf.Representable

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Categoryᴰ

-- TODO: eventually reformulate in terms of profunctors
RightAdjointAtᴰ : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
                  {F : Functor C D}
                  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
                  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
                  {d : D .ob}
                  (R⟅d⟆ : RightAdjointAt' C D F d)
                  (dᴰ : Categoryᴰ.ob[_] Dᴰ d)
                → Type _
RightAdjointAtᴰ {Cᴰ = Cᴰ}{Dᴰ = Dᴰ} Fᴰ R⟅d⟆ dᴰ =
  UniversalElementᴰ Cᴰ ((Dᴰ [-][-, dᴰ ]) ∘Fᴰ (Fᴰ ^opFᴰ)) R⟅d⟆

RightAdjointᴰ : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
                {F : Functor C D}
                {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
                (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
                (R : RightAdjoint' C D F)
              → Type _
RightAdjointᴰ Fᴰ R = ∀ {d} dᴰ → RightAdjointAtᴰ Fᴰ (R d) dᴰ

VerticalRightAdjointAtᴰ : {C : Category ℓC ℓC'}
                     {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
                     (Fᴰ : Functorᴰ Id Cᴰ Dᴰ)
                     {c : C .ob}
                     (cᴰ : Categoryᴰ.ob[_] Dᴰ c)
                     → Type _
VerticalRightAdjointAtᴰ Fᴰ = RightAdjointAtᴰ Fᴰ (IdRightAdj' _ _)

VerticalRightAdjointᴰ : {C : Category ℓC ℓC'}
                     {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
                     (Fᴰ : Functorᴰ Id Cᴰ Dᴰ)
                   → Type _
VerticalRightAdjointᴰ Fᴰ = RightAdjointᴰ Fᴰ (IdRightAdj' _)
