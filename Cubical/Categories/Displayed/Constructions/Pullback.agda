-- Pullback of displayed categories
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Pullback where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Equality as Eq
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.TotalCategory
  as TotalCat

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.TotalCategory
  as TotalCatᴰ
open import Cubical.Categories.Displayed.Constructions.Weaken as Wk
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {E : Category ℓE ℓE'}
         (Cᴰ : Categoryᴰ (C ×C D) ℓCᴰ ℓCᴰ')
         (Dᴰ : Categoryᴰ (D ×C E) ℓDᴰ ℓDᴰ')
       where
  _×pbᴰ_ : Categoryᴰ (C ×C E) _ _
  _×pbᴰ_ = ∫Cᴰ (weaken (C ×C E) D)
    (EqReindex.reindex Cᴰ
      ((BP.Fst C E ∘F TotalCat.Fst {Cᴰ = weaken _ D}) ,F weakenΠ (C ×C E) D)
      Eq.refl (λ _ _ → Eq.refl)
    ×ᴰ EqReindex.reindex Dᴰ
      (weakenΠ (C ×C E) D ,F (BP.Snd C E ∘F TotalCat.Fst {Cᴰ = weaken _ D}))
      Eq.refl (λ _ _ → Eq.refl))
