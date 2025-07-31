{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.Reindex.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Base
  hiding (π; reindex)
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor
open UniversalElement
open UniversalElementᴰ
open UniversalElementⱽ
open CartesianLift

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where
  open isIsoOver
  private
    module C = Category C
    module D = Category D
    F*Dᴰ = Base.reindex Dᴰ F
    module R = HomᴰReasoning Dᴰ
    module F*Dᴰ = Categoryᴰ F*Dᴰ
    module Dᴰ = Categoryᴰ Dᴰ
  -- this definition cannot be η-contracted
  preservesTerminalⱽ :
    ∀ c → Terminalⱽ Dᴰ (F ⟅ c ⟆)
    → Terminalⱽ (Base.reindex Dᴰ F) c
  preservesTerminalⱽ c 𝟙ᴰ .vertexⱽ = 𝟙ᴰ .vertexⱽ
  preservesTerminalⱽ c 𝟙ᴰ .elementⱽ = 𝟙ᴰ .elementⱽ
  preservesTerminalⱽ c 𝟙ᴰ .universalⱽ = 𝟙ᴰ .universalⱽ

  TerminalsⱽReindex : Terminalsⱽ Dᴰ →
    Terminalsⱽ (Base.reindex Dᴰ F)
  TerminalsⱽReindex vtms c = preservesTerminalⱽ c (vtms (F ⟅ c ⟆))

  module _ {c : C .ob} {Fcᴰ Fcᴰ' : Dᴰ.ob[ F ⟅ c ⟆ ]}
    (vbp : BinProductⱽ Dᴰ (Fcᴰ , Fcᴰ')) where
    private
      module Fcᴰ∧Fcᴰ' = BinProductⱽNotation _ vbp

    preservesBinProductⱽ : BinProductⱽ (Base.reindex Dᴰ F) (Fcᴰ , Fcᴰ')
    preservesBinProductⱽ .vertexⱽ = vbp .vertexⱽ
    preservesBinProductⱽ .elementⱽ .fst =
      R.reind (sym $ F .F-id) $ vbp .elementⱽ .fst
    preservesBinProductⱽ .elementⱽ .snd =
      R.reind (sym $ F .F-id) $ vbp .elementⱽ .snd
    preservesBinProductⱽ .universalⱽ .fst (fᴰ₁ , fᴰ₂) = fᴰ₁ Fcᴰ∧Fcᴰ'.,ⱽ fᴰ₂
    preservesBinProductⱽ .universalⱽ .snd .fst (fᴰ₁ , fᴰ₂) = ΣPathP
      ( (R.rectify $ R.≡out $
        (sym $ R.reind-filler _ _)
        ∙ (sym $ R.reind-filler _ _)
        ∙ R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
        ∙ R.reind-filler _ _
        ∙ Fcᴰ∧Fcᴰ'.∫×βⱽ₁)
      , (R.rectify $ R.≡out $
        (sym $ R.reind-filler _ _)
        ∙ (sym $ R.reind-filler _ _)
        ∙ R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
        ∙ R.reind-filler _ _
        ∙ Fcᴰ∧Fcᴰ'.∫×βⱽ₂))
    preservesBinProductⱽ .universalⱽ .snd .snd fᴰ = R.rectify $ R.≡out $
      Fcᴰ∧Fcᴰ'.,ⱽ≡
        (sym (R.reind-filler _ _)
        ∙ sym (R.reind-filler _ _)
        ∙ R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
        ∙ R.reind-filler _ _)
        (sym (R.reind-filler _ _)
        ∙ sym (R.reind-filler _ _)
        ∙ R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
        ∙ R.reind-filler _ _)

  BinProductsⱽReindex : BinProductsⱽ Dᴰ →
    BinProductsⱽ (Base.reindex Dᴰ F)
  BinProductsⱽReindex vps Fcᴰ Fcᴰ×Fcᴰ' =
    preservesBinProductⱽ (vps _ _)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (F : Functor C D)
  (Dᴰ : CartesianCategoryⱽ D ℓDᴰ ℓDᴰ')
  where

  private
    module Dᴰ = CartesianCategoryⱽ Dᴰ
  open CartesianCategoryⱽ
  reindex : CartesianCategoryⱽ C ℓDᴰ ℓDᴰ'
  reindex .Cᴰ = Base.reindex Dᴰ.Cᴰ F
  reindex .termⱽ = TerminalsⱽReindex Dᴰ.termⱽ
  reindex .bpⱽ = BinProductsⱽReindex Dᴰ.bpⱽ
  reindex .cartesianLifts = isFibrationReindex _ _ Dᴰ.cartesianLifts
