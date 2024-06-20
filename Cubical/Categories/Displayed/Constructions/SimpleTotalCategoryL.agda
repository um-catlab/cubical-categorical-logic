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
  hiding (introS)
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq as ReindexEq
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
  hiding (introS; introF)
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
  hiding (intro)
open import Cubical.Categories.Constructions.TotalCategory.More as TotalCat
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryR
  as STotalCatR
  hiding (introS)

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
    module Sym*Cᴰ = EqReindex Cᴰ (BP.Sym {C = C}{D = D})
      Eq.refl (λ _ _ → Eq.refl)

  -- s for "simple" because D is not dependent on C
  -- l for "right" because D is on the left side of the product
  ∫Cᴰsl : Categoryᴰ C _ _
  ∫Cᴰsl = ∫Cᴰsr {C = C} {D = D} Sym*Cᴰ.reindex

  Fstᴰsl : Functorᴰ Id ∫Cᴰsl (weaken C D)
  Fstᴰsl = Fstᴰsr Sym*Cᴰ.reindex

  module _
    {E : Category ℓE ℓE'}
    (F : Functor E C)
    (Fᴰ : Section F (weaken C D))
    (Gᴰ : Section (Sym {C = C}{D = D} ∘F TotalCat.intro' F Fᴰ) Cᴰ)
    where

    open Section

    introS : Section F ∫Cᴰsl
    introS = STotalCatR.introS Sym*Cᴰ.reindex F Fᴰ
      (Sym*Cᴰ.introS _ Gᴰ)

  open Functor
  Assoc-sl⁻ : Functor (∫C ∫Cᴰsl) (∫C Cᴰ)
  Assoc-sl⁻ = ∫F Sym*Cᴰ.forgetReindex ∘F Assoc-sl⁻'
    where
    Assoc-sl⁻' : Functor (∫C ∫Cᴰsl) (∫C Sym*Cᴰ.reindex)
    Assoc-sl⁻' = Assoc {C = C}{D = D} Sym*Cᴰ.reindex
