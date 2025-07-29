{-# OPTIONS --safe --lossy-unification #-}
{- This file takes a *very* long time to type check -}
module Cubical.Categories.Displayed.Limits.BinProduct.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Fibration.Base
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

open import Cubical.Categories.Displayed.Limits.BinProduct.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open UniversalElement
open UniversalElementᴰ
open UniversalElementⱽ
open isIsoOver

module _ {C : Category ℓC ℓC'}{x₁ x₂ : C .ob}
  (prod : BinProduct' C (x₁ , x₂))
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module c×c' = BinProduct'Notation prod
    module R = HomᴰReasoning Cᴰ

  open CartesianLift
  open UniversalElementᴰ

  module _ {xᴰ₁ : Cᴰ.ob[ x₁ ]}{xᴰ₂ : Cᴰ.ob[ x₂ ]}
    (lift-π₁ : CartesianLift Cᴰ xᴰ₁ c×c'.π₁)
    (lift-π₂ : CartesianLift Cᴰ xᴰ₂ c×c'.π₂)
    (vbp : BinProductⱽ Cᴰ ((lift-π₁ .f*yᴰ) , (lift-π₂ .f*yᴰ)))
    where
    open BinProductⱽNotation vbp
    private
      module lift-π₁ = CartesianLift lift-π₁
      module lift-π₂ = CartesianLift lift-π₂
      module vbp = UniversalElementⱽNotation Cᴰ _ _ vbp
    BinProductⱽ→BinProductᴰ : BinProductᴰ Cᴰ prod (xᴰ₁ , xᴰ₂)
    BinProductⱽ→BinProductᴰ .vertexᴰ = vert
    BinProductⱽ→BinProductᴰ .elementᴰ .fst = π₁ Cᴰ.⋆ⱽᴰ (lift-π₁ .π)
    BinProductⱽ→BinProductᴰ .elementᴰ .snd = π₂ Cᴰ.⋆ⱽᴰ (lift-π₂ .π)
    BinProductⱽ→BinProductᴰ .universalᴰ .inv (f₁ , f₂) (fᴰ₁ , fᴰ₂) =
      lift-π₁ .isCartesian .fst (R.reind (sym (c×c'.×β₁)) fᴰ₁)
      ,ⱽ lift-π₂ .isCartesian .fst (R.reind (sym (c×c'.×β₂)) fᴰ₂)
    -- β
    BinProductⱽ→BinProductᴰ .universalᴰ .rightInv (f₁ , f₂) (fᴰ₁ , fᴰ₂) = ΣPathP
      ( (R.rectify $ R.≡out $
        (sym $ R.≡in $ Cᴰ.⋆Assocᴰⱽᴰ)
        ∙ R.⟨ R.≡in ×βⱽ₁ ⟩⋆⟨ refl ⟩
        ∙ lift-π₁.βCL
        ∙ (sym $ R.reind-filler _ _))
      , (R.rectify $ R.≡out $
        (sym $ R.≡in $ Cᴰ.⋆Assocᴰⱽᴰ)
        ∙ R.⟨ R.≡in ×βⱽ₂ ⟩⋆⟨ refl ⟩
        ∙ lift-π₂.βCL
        ∙ (sym $ R.reind-filler _ _)))
    BinProductⱽ→BinProductᴰ .universalᴰ .leftInv f fᴰ = R.rectify $ R.≡out $
      vbp.∫ue.intro≡
        (vbp.Pshⱽ.≡in {p = sym c×c'.×η ∙ (sym $ C.⋆IdR _)} (ΣPathP
          ((Cᴰ.rectify $ Cᴰ.≡out $
            (lift-π₁.introCL≡ (
              (sym $ R.reind-filler _ _)
              ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
              ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
              ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩))
            ∙ (sym $ Cᴰ.reind-filler (C.⋆IdR _ ∙ c×c'.×η) _))
          ,
          (Cᴰ.rectify $ Cᴰ.≡out $
            lift-π₂.introCL≡
              ((sym $ R.reind-filler _ _)
              ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
              ∙ ((sym $ Cᴰ.⋆Assoc _ _ _))
              ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩)
            ∙ (sym $ Cᴰ.reind-filler (C.⋆IdR _ ∙ c×c'.×η) _))
        )))
