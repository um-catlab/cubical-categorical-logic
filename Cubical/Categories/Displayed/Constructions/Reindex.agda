{-

   Given any displayed cat and functor to the base

           A
           |
           |
           |
           |
           ↓
   Δ ----→ Γ
       γ


   There is a universal displayed category over Δ equipped with a
   displayed functor

   γ* A ----→ A
     |        |
     |        |
     |        |
     |        |
     ↓        ↓
     Δ -----→ Γ
        γ


   We write γ* A as reindex (defined upstream).

   The universality says that a section

          γ* A
        ↗ |
       /  |
    M /   |
     /    |
    /     ↓
   Θ ---→ Δ
       δ

   is equivalent to a section

          A
        ↗ |
       /  |
      /   |
     /    |
    /     ↓
   Θ ---→ Γ
      δγ

   that factorizes through the universal displayed functor.

-}
{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Constructions.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq
import      Cubical.Data.Equality.Conversion as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.TotalCategory
  hiding (introS; introF)
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
  hiding (intro)
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Magmoid

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  private
    module C = Category C
    module D = Category D

  open Categoryᴰ Dᴰ
  open Functor F
  open Functorᴰ

  forgetReindex : Functorᴰ F (reindex Dᴰ F) Dᴰ
  forgetReindex .F-obᴰ = λ z → z
  forgetReindex .F-homᴰ = λ z → z
  forgetReindex .F-idᴰ = symP (transport-filler _ _)
  forgetReindex .F-seqᴰ fᴰ gᴰ = symP (transport-filler _ _)

  GlobalSectionReindex→Section : GlobalSection (reindex Dᴰ F) → Section F Dᴰ
  GlobalSectionReindex→Section Fᴰ = compFunctorᴰGlobalSection forgetReindex Fᴰ

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {B : Category ℓB ℓB'}
  (G : Functor B C)
  (FGᴰ : Section (F ∘F G) Dᴰ)
  where
  private
    module R = HomᴰReasoning Dᴰ
  open Functor
  open Section

  introS : Section G (reindex Dᴰ F)
  introS .F-obᴰ = FGᴰ .F-obᴰ
  introS .F-homᴰ = FGᴰ .F-homᴰ
  introS .F-idᴰ = R.≡[]-rectify (R.≡[]∙ _ _ (FGᴰ .F-idᴰ) (R.reind-filler _ _))
  introS .F-seqᴰ fᴰ gᴰ =
    R.≡[]-rectify (R.≡[]∙ _ _ (FGᴰ .F-seqᴰ fᴰ gᴰ) (R.reind-filler _ _))

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {B : Category ℓB ℓB'} {Bᴰ : Categoryᴰ B ℓBᴰ ℓBᴰ'}
  (G : Functor B C)
  (FGᴰ : Functorᴰ (F ∘F G) Bᴰ Dᴰ)
  where
  introF : Functorᴰ G Bᴰ (reindex Dᴰ F)
  introF = TotalCat.recᴰ _ _ (introS _
    (reindS' (Eq.refl , Eq.refl) (TotalCat.elim FGᴰ)))
