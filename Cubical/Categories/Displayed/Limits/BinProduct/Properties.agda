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
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Presheaf.CartesianLift
import Cubical.Categories.Displayed.Fibration.Base as CatFib
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

open import Cubical.Categories.Displayed.Limits.BinProduct.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓPᴰ ℓQ ℓQᴰ : Level

open Category
open UniversalElement
open UniversalElementᴰ
open Bifunctorᴰ
open isIsoOver
open PshHomᴰ
open Functor

-- to use paths we need everything to be at the same universe level
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓC'}{Q : Presheaf C ℓC'}
  {Pᴰ : Presheafᴰ P Cᴰ ℓCᴰ'} {Qᴰ : Presheafᴰ Q Cᴰ ℓCᴰ'}
  (p×q : Representationᵁ C (P ×Psh Q))
  where
  private
    π₁₂ = (transport (cong fst $ funExt⁻ (cong F-ob (p×q .snd)) _) (C .id))
    module PSHᴰ = Categoryᴰ (PRESHEAFᴰ Cᴰ ℓCᴰ ℓCᴰ')

  module _
    (π₁* : Representationᵁⱽ Cᴰ (reindYo (π₁ P Q .fst _ π₁₂) Pᴰ))
    (π₂* : Representationᵁⱽ Cᴰ (reindYo (π₂ P Q .fst _ π₁₂) Qᴰ))
    where
    ×ᴰ≡π₁*×ⱽπ₂* :
      PathP (λ i → Presheafᴰ (p×q .snd i) Cᴰ ℓCᴰ')
        ((Cᴰ [-][-, π₁* .fst ]) ×ⱽPsh (Cᴰ [-][-, π₂* .fst ]))
        (Pᴰ ×ᴰPsh Qᴰ)
    ×ᴰ≡π₁*×ⱽπ₂* =
      cong₂ _×ⱽPsh_
        (π₁* .snd ∙ (sym $ reindYo-seq (π₁ _ Q) _ π₁₂) ∙ cong₂ reind (sym (pathToPshIsoYo (p×q .snd))) refl)
        (π₂* .snd ∙ (sym $ reindYo-seq (π₂ P Q) _ π₁₂) ∙ cong₂ reind ((sym (pathToPshIsoYo (p×q .snd)))) refl)
      ◁
      (λ i → reindPathToPshIsoPathP (p×q .snd) (reind (π₁ P Q) Pᴰ) i
             ×ⱽPsh reindPathToPshIsoPathP (p×q .snd) (reind (π₂ P Q) Qᴰ) i)
      ▷ sym (PshProdⱽ≡ᴰ Pᴰ Qᴰ)

-- It involves a lot more manual combinators, but we can do this
-- entirely with PshIso and be fully universe polymorphic
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  (p×q : UniversalElement C (P ×Psh Q))
  (π₁* : UniversalElementⱽ Cᴰ _ (reindYo (p×q .element .fst) Pᴰ))
  (π₂* : UniversalElementⱽ Cᴰ _ (reindYo (p×q .element .snd) Qᴰ))
  (π₁*×ⱽπ₂* : UniversalElementⱽ Cᴰ _
    ((Cᴰ [-][-, (π₁* .UniversalElementⱽ.vertexᴰ) ]) ×ⱽPsh (Cᴰ [-][-, (π₂* .UniversalElementⱽ.vertexᴰ) ])))
  where

  ×ᴰ≅π₁*×ⱽπ₂* :
    PshIsoᴰ (yoRecIso p×q)
      ((Cᴰ [-][-, (π₁* .UniversalElementⱽ.vertexᴰ) ]) ×ⱽPsh (Cᴰ [-][-, (π₂* .UniversalElementⱽ.vertexᴰ) ]))
      (Pᴰ ×ᴰPsh Qᴰ)
  ×ᴰ≅π₁*×ⱽπ₂* =
    -- TODO: get these fixities right
    ((yoRecIsoⱽ π₁* ⋆PshIsoⱽ (pathToPshIsoⱽ (cong₂ reind (sym $ yoRec-natural _ _ _) refl) ⋆PshIsoⱽ invPshIsoⱽ (reind-seqIsoⱽ _ _ _)))
    ×ⱽIso ((yoRecIsoⱽ π₂* ⋆PshIsoⱽ (pathToPshIsoⱽ (cong₂ reind (sym $ yoRec-natural _ _ _) refl) ⋆PshIsoⱽ invPshIsoⱽ (reind-seqIsoⱽ _ _ _)))))
    ⋆PshIsoⱽᴰ ((reindPshIsoPshIsoᴰ _ _ ×ⱽIso reindPshIsoPshIsoᴰ _ _)
    ⋆PshIsoᴰⱽ invPshIsoⱽ (PshProdⱽ≅ᴰ Pᴰ Qᴰ))

  ×ⱽRepr+π*→×ᴰRepr : UniversalElementᴰ Cᴰ p×q (Pᴰ ×ᴰPsh Qᴰ)
  ×ⱽRepr+π*→×ᴰRepr = π₁*×ⱽπ₂* ◃PshIsoⱽᴰ ×ᴰ≅π₁*×ⱽπ₂*

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

  BinProductⱽ→PshProdReprᴰ : UniversalElementᴰ Cᴰ P×Q (Pᴰ ×ᴰPsh Qᴰ)
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
    (lift-π₁ : CatFib.CartesianLift Cᴰ xᴰ₁ c×c'.π₁)
    (lift-π₂ : CatFib.CartesianLift Cᴰ xᴰ₂ c×c'.π₂)
    (vbp : BinProductⱽ Cᴰ ((lift-π₁ .CatFib.CartesianLift.f*yᴰ) , (lift-π₂ .CatFib.CartesianLift.f*yᴰ)))
    where
    BinProductⱽ→BinProductᴰ : BinProductᴰ Cᴰ prod (xᴰ₁ , xᴰ₂)
    BinProductⱽ→BinProductᴰ =
      ×ⱽRepr+π*→×ᴰRepr prod
        (CartesianLift→CartesianLift' _ _ (CatLift→YoLift lift-π₁))
        (CartesianLift→CartesianLift' _ _ (CatLift→YoLift lift-π₂))
        vbp

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (cartesianLifts : CatFib.isFibration Cᴰ)
  (bpⱽ : BinProductsⱽ Cᴰ) (bp : BinProducts C)
  where

  BinProductsⱽ→BinProductsᴰ : BinProductsᴰ Cᴰ bp
  BinProductsⱽ→BinProductsᴰ cᴰ12 =
    BinProductⱽ→BinProductᴰ (bp _) Cᴰ
      (cartesianLifts _ _) (cartesianLifts _ _) (bpⱽ _ _)
