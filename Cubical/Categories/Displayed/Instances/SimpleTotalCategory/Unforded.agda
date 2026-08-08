{-# OPTIONS --lossy-unification #-}
{-

  THE UN-FORDED RE-ASSOCIATORS, for comparison with
  .SimpleTotalCategory.Forded.

  Instances.SimpleTotalCategoryR leaves

    Assoc : Functor (∫C ∫Cᴰsr) (∫C Cᴰ)
    Assoc = {!!}

  as a hole (commented out), and Instances.SimpleTotalCategoryL
  comments out `Assoc-sl⁻` because it depends on that hole.  Both are
  in fact definable with the machinery already in the library: the
  generic re-associator `Assocᴰ` of
  Displayed.Instances.TotalCategory lands in `∫C Cᴰ'.reindex` rather
  than in `∫C Cᴰ`, and the missing step is exactly `∫F` of the
  `EqReindex` module's own `forgetReindex`.

  So the hole was not an obstruction --- it was unfinished.  What the
  forded development in .Forded buys is not definability but
  UNIFORMITY: there, R and L are one definition applied to two strict
  functors, `∫ᶠsl Cᴰ ≡ ∫ᶠsr (reindexS Symᶠ Cᴰ)` holds by `refl`, and no
  `EqReindex` (hence no `Eq.transport`, no `singl`) appears anywhere.

-}
module Cubical.Categories.Displayed.Instances.SimpleTotalCategory.Unforded
  where

open import Cubical.Foundations.Prelude
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.TotalCategory as TotalCat
  hiding (intro)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Weaken.Base
open import Cubical.Categories.Displayed.Instances.Weaken.Properties
open import Cubical.Categories.Displayed.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.SimpleTotalCategoryR

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Cᴰ : Categoryᴰ (C ×C D) ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ' = EqReindex Cᴰ ∫wk→× Eq.refl (λ _ _ → Eq.refl)

  AssocStock : Functor (∫C (∫Cᴰsr Cᴰ)) (∫C Cᴰ)
  AssocStock = ∫F Cᴰ'.forgetReindex ∘F Assocᴰ {Cᴰ = weaken C D} Cᴰ'.reindex

open import Cubical.Categories.Displayed.Instances.SimpleTotalCategoryL

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Cᴰ : Categoryᴰ (D ×C C) ℓCᴰ ℓCᴰ') where
  private
    module Sym*Cᴰ =
      EqReindex Cᴰ (Sym {C = C} {D = D}) Eq.refl (λ _ _ → Eq.refl)

  AssocStockL : Functor (∫C (∫Cᴰsl Cᴰ)) (∫C Cᴰ)
  AssocStockL = ∫F Sym*Cᴰ.forgetReindex ∘F AssocStock Sym*Cᴰ.reindex
