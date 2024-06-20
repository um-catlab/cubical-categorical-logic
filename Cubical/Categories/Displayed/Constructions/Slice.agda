{-

  The slice category over a displayed category. Used in the definition
  of a fibration.

-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Slice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import      Cubical.Data.Equality as Eq
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Constructions.TotalCategory.More as TotalCat
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Displayed.Constructions.TotalCategory
  as TotalCatᴰ
open import Cubical.Categories.Displayed.Constructions.TotalCategory.More
  as TotalCatᴰ
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.BinProduct.More as BP
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base as Disp
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq as Reindex
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More as BPᴰ
open import Cubical.Categories.Displayed.Properties as Disp
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Hom
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Displayed.Section.Base
private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Categoryᴰ
open Functor

module _ (C : Category ℓC ℓC') (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private module Slice = EqReindex Cᴰ (BP.Snd C C) Eq.refl (λ _ _ → Eq.refl)
  -- See test below for the intuitive definition
  _/C_ : Categoryᴰ C _ _
  _/C_ = ∫Cᴰ (weaken C C) (Cᴰ' ×ᴰ Hom C)
    where Cᴰ' = Slice.reindex

  private
    open Category
    open Categoryᴰ
    test : ∀ {c} → _/C_ .ob[_] c ≡ (Σ[ c' ∈ C .ob ] Cᴰ .ob[_] c' × C [ c , c' ])
    test = refl

  Δ/C : Functorᴰ Id Cᴰ _/C_
  Δ/C = TotalCatᴰ.introF _ _ (Wk.introF Id Id)
    (BPᴰ.introS _
      (Slice.introS _ (reindS' (Eq.refl , Eq.refl) TotalCat.Snd))
      (reindS' (Eq.refl , Eq.refl)
        (compSectionFunctor ID (TotalCat.Fst {Cᴰ = Cᴰ}))))

  private
    open Functorᴰ
    _ : ∀ c (cᴰ : Cᴰ .ob[_] c) → Δ/C .F-obᴰ cᴰ ≡ (c , (cᴰ , C .id))
    _ = λ c cᴰ → refl

module _ (C : Category ℓC ℓC') where
  -- Slices .ob[ c ] = Σ[ c' ∈ C .ob] C [ c' , c ]
  Slices : Categoryᴰ C (ℓ-max ℓC ℓC') (ℓ-max ℓC' ℓC')
  Slices = ∫Cᴰ (weaken C C) (Hom C)

  private
    open Category
    open Categoryᴰ
    test : ∀ {c} → Slices .ob[_] c ≡ (Σ[ c' ∈ C .ob ] C [ c , c' ])
    test = refl

  Subobjects : Categoryᴰ C _ _
  Subobjects = ∫Cᴰ (weaken C C) (Mono C)
  private
    open Category
    open Categoryᴰ
    test' : ∀ {c} → Subobjects .ob[_] c
      ≡ (Σ[ c' ∈ C .ob ] Σ[ f ∈ C [ c , c' ] ] isMonic C f)
    test' = refl
