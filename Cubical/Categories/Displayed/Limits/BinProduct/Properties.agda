{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Limits.BinProduct.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Fibration
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
open PshHom
open PshIso
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
    (π₁* : Representationᵁⱽ Cᴰ (reindYo (π₁ P Q .N-ob _ π₁₂) Pᴰ))
    (π₂* : Representationᵁⱽ Cᴰ (reindYo (π₂ P Q .N-ob _ π₁₂) Qᴰ))
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
    ((((yoRecIsoⱽ π₁*
        ⋆PshIsoⱽ pathToPshIsoⱽ (cong₂ reind (sym $ yoRec-natural _ _ _) refl)
        ⋆PshIsoⱽ invPshIsoⱽ (reind-seqIsoⱽ _ (π₁ P Q) _))
      ×ⱽIso
      ((yoRecIsoⱽ π₂*
        ⋆PshIsoⱽ pathToPshIsoⱽ (cong₂ reind (sym $ yoRec-natural _ _ _) refl))
        ⋆PshIsoⱽ invPshIsoⱽ (reind-seqIsoⱽ _ (π₂ P Q) _)))
    ⋆PshIsoⱽᴰ (reindPshIsoPshIsoᴰ _ _ ×ⱽIso reindPshIsoPshIsoᴰ _ _))
    ⋆PshIsoᴰⱽ invPshIsoⱽ (PshProdⱽ≅ᴰ Pᴰ Qᴰ))

  ×ⱽRepr+π*→×ᴰRepr : UniversalElementᴰ Cᴰ p×q (Pᴰ ×ᴰPsh Qᴰ)
  ×ⱽRepr+π*→×ᴰRepr = π₁*×ⱽπ₂* ◁PshIsoⱽᴰ ×ᴰ≅π₁*×ⱽπ₂*

module _ {C : Category ℓC ℓC'}{x₁ x₂ : C .ob}
  (prod : BinProduct C (x₁ , x₂))
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module c×c' = BinProductNotation prod
    module R = HomᴰReasoning Cᴰ

  open UniversalElementⱽ
  module _ {xᴰ₁ : Cᴰ.ob[ x₁ ]}{xᴰ₂ : Cᴰ.ob[ x₂ ]}
    (lift-π₁ : CartesianLift Cᴰ xᴰ₁ c×c'.π₁)
    (lift-π₂ : CartesianLift Cᴰ xᴰ₂ c×c'.π₂)
    (vbp : BinProductⱽ Cᴰ (lift-π₁ .vertexⱽ , lift-π₂ .vertexⱽ))
    where
    BinProductⱽ→BinProductᴰ : BinProductᴰ Cᴰ prod (xᴰ₁ , xᴰ₂)
    BinProductⱽ→BinProductᴰ =
      vbp
      ◁PshIsoⱽᴰ ×ᴰ≅π₁*×ⱽπ₂*
        prod
        (lift-π₁)
        (lift-π₂)
        vbp

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (cartesianLifts : isFibration Cᴰ)
  (bpⱽ : BinProductsⱽ Cᴰ) (bp : BinProducts C)
  where

  BinProductsⱽ→BinProductsᴰ : BinProductsᴰ Cᴰ bp
  BinProductsⱽ→BinProductsᴰ cᴰ12 =
    BinProductⱽ→BinProductᴰ (bp _) Cᴰ
      (cartesianLifts _ _) (cartesianLifts _ _) (bpⱽ _ _)
