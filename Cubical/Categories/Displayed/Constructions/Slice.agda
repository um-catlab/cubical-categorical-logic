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
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Displayed.Constructions.TotalCategory
  as TotalCatᴰ hiding (introF)
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.BinProduct.More as BP
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base as Disp
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
  hiding (introF)
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq as Reindex
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More as BPᴰ
  hiding (introF)
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Arrow
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
  hiding (introF)
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
  private
    module wkCᴰ = EqReindex Cᴰ (weakenΠ C _) Eq.refl (λ _ _ → Eq.refl)
    module Arrow' = EqReindex (Arrow C) (TotalCat.Fst ,F weakenΠ C _) Eq.refl (λ _ _ → Eq.refl)
  -- See test below for the intuitive definition
  _/C_ : Categoryᴰ C _ _
  _/C_ = ∫Cᴰ (weaken C C) (wkCᴰ.reindex ×ᴰ Arrow'.reindex)

  module _ {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    {F : Functor D C}
    (Fᴰ₁ : Functor D C)
    (Fᴰ₂ : Functorᴰ Fᴰ₁ Dᴰ Cᴰ)
    (Fᴰ₃ : F ⇒ Fᴰ₁)
    where
    -- NOTE: this is not the most general introduction rule possible.
    -- A more general version would allow Fᴰ₁ to depend on Dᴰ as well.
    introF : Functorᴰ F Dᴰ _/C_
    introF = TotalCatᴰ.introF _ _ (Wk.introF F Fᴰ₁)
      (BPᴰ.introS _
        (wkCᴰ.introS _ (reindS' (Eq.refl , Eq.refl) (TotalCat.elim Fᴰ₂)))
        (Arrow'.introS _
        (reindS' (Eq.refl , Eq.refl)
          (compSectionFunctor (arrIntroS Fᴰ₃)
            TotalCat.Fst)) ))

  private
    open Category
    open Categoryᴰ
    test : ∀ {c} → _/C_ .ob[_] c ≡ (Σ[ c' ∈ C .ob ] Cᴰ .ob[_] c' × C [ c , c' ])
    test = refl

  Δ/C : Functorᴰ Id Cᴰ _/C_
  Δ/C = introF Id 𝟙ᴰ⟨ Cᴰ ⟩ (idTrans Id)

  private
    open Functorᴰ
    _ : ∀ c (cᴰ : Cᴰ .ob[_] c) → Δ/C .F-obᴰ cᴰ ≡ (c , (cᴰ , C .id))
    _ = λ c cᴰ → refl

module _ (C : Category ℓC ℓC') where
  private
    module Arrow' = EqReindex (Arrow C) (TotalCat.Fst ,F weakenΠ C _) Eq.refl (λ _ _ → Eq.refl)
    module Mono' = EqReindex (Mono C) (TotalCat.Fst ,F weakenΠ C _) Eq.refl (λ _ _ → Eq.refl)
  -- Slices .ob[ c ] = Σ[ c' ∈ C .ob] C [ c' , c ]
  Slices : Categoryᴰ C (ℓ-max ℓC ℓC') (ℓ-max ℓC' ℓC')
  Slices = ∫Cᴰ (weaken C C) Arrow'.reindex

  private
    open Category
    open Categoryᴰ
    test : ∀ {c} → Slices .ob[_] c ≡ (Σ[ c' ∈ C .ob ] C [ c , c' ])
    test = refl

  Subobjects : Categoryᴰ C _ _
  Subobjects = ∫Cᴰ (weaken C C) Mono'.reindex
  private
    open Category
    open Categoryᴰ
    test' : ∀ {c} → Subobjects .ob[_] c
      ≡ (Σ[ c' ∈ C .ob ] Σ[ f ∈ C [ c , c' ] ] isMonic C f)
    test' = refl
