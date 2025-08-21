{-# OPTIONS --lossy-unification #-}
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
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Presheaf.CartesianLift
open import Cubical.Categories.Displayed.Fibration.Base
  renaming (isFibration to isCatFibration; CartesianLift to CatCartesianLift)
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

open import Cubical.Categories.Displayed.Limits.BinProduct.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓPᴰ ℓQ ℓQᴰ : Level

open Category
open UniversalElement
open UniversalElementᴰ
open UniversalElementⱽ
open Bifunctorᴰ
open isIsoOver

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  (P×Q : UniversalElement C (PshProd ⟅ P , Q ⟆b))
  (lift-π₁ : CartesianLift (P×Q .element .fst) Pᴰ)
  (lift-π₂ : CartesianLift (P×Q .element .snd) Qᴰ)
  (bpⱽ : BinProductⱽ Cᴰ (lift-π₁ .CartesianLift.p*Pᴰ , lift-π₂ .CartesianLift.p*Pᴰ))
  where

  private
    module π₁*P = CartesianLift lift-π₁
    module π₂*Q = CartesianLift lift-π₂
    module bpⱽ = BinProductⱽNotation _ bpⱽ
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    module P×Q = UniversalElementNotation P×Q
    module Cᴰ = Fibers Cᴰ

  BinProductⱽ→PshProdReprᴰ : UniversalElementᴰ Cᴰ P×Q (PshProdᴰ .Bif-obᴰ Pᴰ Qᴰ)
  BinProductⱽ→PshProdReprᴰ .vertexᴰ = bpⱽ.vert
  BinProductⱽ→PshProdReprᴰ .elementᴰ .fst = bpⱽ.π₁ Pᴰ.⋆ⱽᴰ π₁*P.π
  BinProductⱽ→PshProdReprᴰ .elementᴰ .snd = bpⱽ.π₂ Qᴰ.⋆ⱽᴰ π₂*Q.π
  BinProductⱽ→PshProdReprᴰ .universalᴰ .inv (f₁ , f₂) (fᴰ₁ , fᴰ₂) =
    π₁*P.intro (Pᴰ.reind (sym $ cong fst $ P×Q.β) fᴰ₁) bpⱽ.,ⱽ π₂*Q.intro (Qᴰ.reind (sym $ cong snd $ P×Q.β) fᴰ₂)
  BinProductⱽ→PshProdReprᴰ .universalᴰ .rightInv (f₁ , f₂) (fᴰ₁ , fᴰ₂) = ΣPathP
    ( (Pᴰ.rectify $ Pᴰ.≡out $
      (sym $ Pᴰ.⋆Assocᴰⱽᴰ _ _ _)
      ∙ Pᴰ.⟨ bpⱽ.∫×βⱽ₁ ⟩⋆⟨ refl ⟩
      ∙ π₁*P.β
      ∙ (sym $ Pᴰ.reind-filler _ _)
      )
    , (Qᴰ.rectify $ Qᴰ.≡out $
      (sym $ Qᴰ.⋆Assocᴰⱽᴰ _ _ _)
      ∙ Qᴰ.⟨ bpⱽ.∫×βⱽ₂ ⟩⋆⟨ refl ⟩
      ∙ π₂*Q.β
      ∙ (sym $ Qᴰ.reind-filler _ _)))
  BinProductⱽ→PshProdReprᴰ .universalᴰ .leftInv f fᴰ = Cᴰ.rectify $ Cᴰ.≡out $
    bpⱽ.,ⱽ≡
      (π₁*P.intro≡
        ((sym $ Pᴰ.reind-filler _ _)
        ∙ Pᴰ.⟨ refl ⟩⋆⟨ sym $ Pᴰ.reind-filler _ _ ⟩
        ∙ (sym $ Pᴰ.⋆Assoc _ _ _)
        ∙ Pᴰ.⟨ Cᴰ.reind-filler _ _ ∙ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩)
        ∙ (sym $ Cᴰ.reind-filler P×Q.η _))
      (π₂*Q.intro≡
        ((sym $ Qᴰ.reind-filler _ _)
        ∙ Qᴰ.⟨ refl ⟩⋆⟨ sym $ Qᴰ.reind-filler _ _ ⟩
        ∙ (sym $ Qᴰ.⋆Assoc _ _ _)
        ∙ Qᴰ.⟨ Cᴰ.reind-filler _ _ ∙ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩)
        ∙ (sym $ Cᴰ.reind-filler P×Q.η _))

module _ {C : Category ℓC ℓC'}{x₁ x₂ : C .ob}
  (prod : BinProduct C (x₁ , x₂))
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module c×c' = BinProductNotation prod
    module R = HomᴰReasoning Cᴰ

  open UniversalElementᴰ
  module _ {xᴰ₁ : Cᴰ.ob[ x₁ ]}{xᴰ₂ : Cᴰ.ob[ x₂ ]}
    (lift-π₁ : CatCartesianLift Cᴰ xᴰ₁ c×c'.π₁)
    (lift-π₂ : CatCartesianLift Cᴰ xᴰ₂ c×c'.π₂)
    (vbp : BinProductⱽ Cᴰ ((lift-π₁ .CatCartesianLift.f*yᴰ) , (lift-π₂ .CatCartesianLift.f*yᴰ)))
    where
    BinProductⱽ→BinProductᴰ : BinProductᴰ Cᴰ prod (xᴰ₁ , xᴰ₂)
    BinProductⱽ→BinProductᴰ =
      BinProductⱽ→PshProdReprᴰ prod
        (CatLift→YoLift lift-π₁) (CatLift→YoLift lift-π₂)
        vbp
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (cartesianLifts : isCatFibration Cᴰ)
  (bpⱽ : BinProductsⱽ Cᴰ) (bp : BinProducts C)
  where

  BinProductsⱽ→BinProductsᴰ : BinProductsᴰ Cᴰ bp
  BinProductsⱽ→BinProductsᴰ cᴰ12 =
    BinProductⱽ→BinProductᴰ (bp _) Cᴰ
      (cartesianLifts _ _) (cartesianLifts _ _) (bpⱽ _ _)
