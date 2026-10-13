{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Reindex.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Instances.Fiber

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Base as Base
  hiding (π; reindex)
open import Cubical.Categories.Displayed.Instances.Reindex.CurriedFibration
open import Cubical.Categories.Displayed.Limits.CartesianV
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Constructions.Unit

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor
open UniversalElement
open UniversalElementᴰ
open UniversalElementⱽ

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where
  open isIsoOver
  private
    module C = Category C
    module D = Category D
    F*Dᴰ = Base.reindex Dᴰ F
    module F*Dᴰ = Categoryᴰ F*Dᴰ
    module Dᴰ = Fibers Dᴰ
  -- this definition cannot be η-contracted
    preservesTerminalⱽ :
      ∀ c → Terminalⱽ Dᴰ (F ⟅ c ⟆)
      → Terminalⱽ (Base.reindex Dᴰ F) c
    preservesTerminalⱽ c 𝟙ᴰ .vertexⱽ = 𝟙ᴰ .vertexⱽ
    preservesTerminalⱽ c 𝟙ᴰ .elementⱽ = 𝟙ᴰ .elementⱽ
    preservesTerminalⱽ c 𝟙ᴰ .universalⱽ = 𝟙ᴰ .universalⱽ

  TerminalⱽReindex : ∀ {c}
    → Terminalⱽ Dᴰ (F ⟅ c ⟆)
    → Terminalⱽ (Base.reindex Dᴰ F) c
  TerminalⱽReindex 𝟙Fc =
    reindUEⱽ 𝟙Fc
    ◁PshIsoⱽ (reindPshIsoⱽ (Functor→PshHet F _) (reindPshᴰFunctorUnitIsoⱽ (Base.π Dᴰ F))
    ⋆PshIsoⱽ reindUnitIsoⱽ)

  TerminalsⱽReindex : Terminalsⱽ Dᴰ →
    Terminalsⱽ (Base.reindex Dᴰ F)
  TerminalsⱽReindex vtms c = TerminalⱽReindex (vtms (F ⟅ c ⟆))

  module _ {c : C .ob} {Fcᴰ Fcᴰ' : Dᴰ.ob[ F ⟅ c ⟆ ]}
    (vbp : BinProductⱽ Dᴰ (Fcᴰ , Fcᴰ')) where
    private
      module Fcᴰ∧Fcᴰ' = BinProductⱽNotation _ vbp

      opaque
        unfolding hSetReasoning.reind
        preservesBinProductⱽ : BinProductⱽ (Base.reindex Dᴰ F) (Fcᴰ , Fcᴰ')
        preservesBinProductⱽ .vertexⱽ = vbp .vertexⱽ
        preservesBinProductⱽ .elementⱽ .fst =
          Dᴰ.reind (sym $ F .F-id) $ vbp .elementⱽ .fst
        preservesBinProductⱽ .elementⱽ .snd =
          Dᴰ.reind (sym $ F .F-id) $ vbp .elementⱽ .snd
        preservesBinProductⱽ .universalⱽ .fst (fᴰ₁ , fᴰ₂) = fᴰ₁ Fcᴰ∧Fcᴰ'.,ⱽ fᴰ₂
        preservesBinProductⱽ .universalⱽ .snd .fst (fᴰ₁ , fᴰ₂) = ΣPathP
          ( (Dᴰ.rectify $ Dᴰ.≡out $
            (sym $ Dᴰ.reind-filler _)
            ∙ (sym $ Dᴰ.reind-filler _)
            ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ ⟩
            ∙ Dᴰ.reind-filler _
            ∙ Fcᴰ∧Fcᴰ'.∫×βⱽ₁)
          , (Dᴰ.rectify $ Dᴰ.≡out $
            (sym $ Dᴰ.reind-filler _)
            ∙ (sym $ Dᴰ.reind-filler _)
            ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ ⟩
            ∙ Dᴰ.reind-filler _
            ∙ Fcᴰ∧Fcᴰ'.∫×βⱽ₂))
        preservesBinProductⱽ .universalⱽ .snd .snd fᴰ = Dᴰ.rectify $ Dᴰ.≡out $
          Fcᴰ∧Fcᴰ'.,ⱽ≡
            (sym (Dᴰ.reind-filler _)
            ∙ sym (Dᴰ.reind-filler _)
            ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ ⟩
            ∙ Dᴰ.reind-filler _)
            (sym (Dᴰ.reind-filler _)
            ∙ sym (Dᴰ.reind-filler _)
            ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ ⟩
            ∙ Dᴰ.reind-filler _)

    BinProductⱽReindex : BinProductⱽ (Base.reindex Dᴰ F) (Fcᴰ , Fcᴰ')
    BinProductⱽReindex =
      -- the annotations on reindⱽFuncRepr are crucial for performance
      reindUEⱽ vbp
        ◁PshIsoⱽ
        (reindⱽFunc×ⱽIsoⱽ ⋆PshIsoⱽ (reindⱽFuncRepr {xᴰ = Fcᴰ} ×ⱽIso reindⱽFuncRepr {Dᴰ = Dᴰ} {F = F} {xᴰ = Fcᴰ'}))
  BinProductsⱽReindex : BinProductsⱽ Dᴰ →
    BinProductsⱽ (Base.reindex Dᴰ F)
  BinProductsⱽReindex vps Fcᴰ Fcᴰ×Fcᴰ' =
    BinProductⱽReindex (vps _ _)

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
  reindex .cartesianLifts = isFibrationReindex _ Dᴰ.cartesianLifts
