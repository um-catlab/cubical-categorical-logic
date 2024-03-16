{-
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryL where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.BinProduct.More as BP
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Displayed.Constructions.Reindex as Reindex
  hiding (intro)
open import Cubical.Categories.Displayed.Constructions.Weaken as Wk
  hiding (intro)
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Terminal hiding (intro)
open import Cubical.Categories.Displayed.Base.More as TotalCat
open import Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryR
  as STotalCatR
  hiding (intro)

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ

-- Given a displayed category over a product of two categories,
-- we can project out the two categories and
-- then display over them.
module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Cᴰ : Categoryᴰ (D ×C C) ℓCᴰ ℓCᴰ')
  where
  open Category

  private
    module Cᴰ = Categoryᴰ Cᴰ
    Sym*Cᴰ = (reindex' Cᴰ (BP.Sym {C = C}{D = D}) Eq.refl λ _ _ → Eq.refl)

  -- s for "simple" because D is not dependent on C
  -- l for "right" because D is on the left side of the product
  ∫Cᴰsl : Categoryᴰ C _ _
  ∫Cᴰsl = ∫Cᴰsr {C = C} {D = D} Sym*Cᴰ

  Fstᴰsl : Functorᴰ Id ∫Cᴰsl (weaken C D)
  Fstᴰsl = Fstᴰsr Sym*Cᴰ

  module _
    {E : Category ℓE ℓE'}
    (F : Functor E C)
    {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
    (Fᴰ : Functorᴰ F Eᴰ (weaken C D))
    (Gᴰ : Functorᴰ (Sym {C = C}{D = D} ∘F ∫F Fᴰ) (Unitᴰ (∫C Eᴰ)) Cᴰ)
    where
    open Functorᴰ

    intro : Functorᴰ F Eᴰ ∫Cᴰsl
    intro = STotalCatR.intro Sym*Cᴰ F Fᴰ
      (reindex-intro' Cᴰ (BP.Sym {C = C}{D = D}) Eq.refl (λ _ _ → Eq.refl)
        (∫F {F = F} Fᴰ)
        Gᴰ)

  open Functor
  Assoc-sl⁻ : Functor (∫C ∫Cᴰsl) (∫C Cᴰ)
  Assoc-sl⁻ = ∫F {C = C ×C D}{D = D ×C C}{F = BP.Sym {C = C}{D = D}}
              (forgetReindex' Cᴰ (BP.Sym {C = C}{D = D})
                Eq.refl λ _ _ → Eq.refl)
            ∘F Assoc-sl⁻'
    where
    Assoc-sl⁻' : Functor (∫C ∫Cᴰsl) (∫C Sym*Cᴰ)
    Assoc-sl⁻' = Assoc-sr⁻ {C = C}{D = D} Sym*Cᴰ
