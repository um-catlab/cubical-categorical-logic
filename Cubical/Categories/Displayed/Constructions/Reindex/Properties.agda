{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Constructions.Reindex.Properties where

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
open import Cubical.Categories.Displayed.Constructions.Reindex.Base hiding (π)
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
open UniversalElementᵛ
open CartesianLift

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  private
    module C = Category C
    module D = Category D
    F*Dᴰ = reindex Dᴰ F
    module R = HomᴰReasoning Dᴰ
    module F*Dᴰ = Categoryᴰ F*Dᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  hasPropHomsReindex : hasPropHoms Dᴰ → hasPropHoms (reindex Dᴰ F)
  hasPropHomsReindex = λ z {c} {c'} f → z (F-hom F f)

  module _
    {c : C .ob}{c' : C .ob}
    {dᴰ' : Dᴰ.ob[ F ⟅ c' ⟆ ]}{f : C [ c , c' ]}
    where
    reflectsCartesianLifts
      : CartesianLift Dᴰ dᴰ' (F ⟪ f ⟫)
      → CartesianLift F*Dᴰ dᴰ' f
    reflectsCartesianLifts F⟪f⟫-lift .f*yᴰ = F⟪f⟫-lift .f*yᴰ
    reflectsCartesianLifts F⟪f⟫-lift .π = F⟪f⟫-lift .π
    reflectsCartesianLifts F⟪f⟫-lift .isCartesian .fst gfᴰ =
      F⟪f⟫-lift .isCartesian .fst (R.reind (F .F-seq _ _) gfᴰ)
    reflectsCartesianLifts F⟪f⟫-lift .isCartesian .snd .fst gfᴰ = R.rectify $ R.≡out $
      (sym $ R.reind-filler _ _)
      ∙ (R.≡in $ F⟪f⟫-lift .isCartesian .snd .fst _)
      ∙ (sym $ R.reind-filler _ _)

    reflectsCartesianLifts F⟪f⟫-lift .isCartesian .snd .snd gᴰ = R.rectify $ R.≡out $
      ((R.≡in $ congP (λ _ → F⟪f⟫-lift .isCartesian .fst)
        -- TODO: add reindReind⁻ to Reasoning
        $ transportTransport⁻ (λ i → Dᴰ.Hom[ F .F-seq _ _ i ][ _ , _ ]) (gᴰ Dᴰ.⋆ᴰ F⟪f⟫-lift .π)) 
      ∙ (R.≡in $ F⟪f⟫-lift .isCartesian .snd .snd gᴰ))

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where
  open isIsoOver
  private
    module C = Category C
    module D = Category D
    F*Dᴰ = reindex Dᴰ F
    module R = HomᴰReasoning Dᴰ
    module F*Dᴰ = Categoryᴰ F*Dᴰ
    module Dᴰ = Categoryᴰ Dᴰ
  preservesVerticalTerminal :
    ∀ c → VerticalTerminalAt Dᴰ (F ⟅ c ⟆)
    → VerticalTerminalAt (reindex Dᴰ F) c
  preservesVerticalTerminal c 𝟙ᴰ .vertexᴰ = 𝟙ᴰ .vertexᴰ
  preservesVerticalTerminal c 𝟙ᴰ .elementᴰ = 𝟙ᴰ .elementᴰ
  preservesVerticalTerminal c 𝟙ᴰ .universalᴰ .inv f _ = introᴰ 𝟙ᴰ (F ⟪ f ⟫) _
  preservesVerticalTerminal c 𝟙ᴰ .universalᴰ .rightInv _ _ = refl
  preservesVerticalTerminal c 𝟙ᴰ .universalᴰ {xᴰ = xᴰ} .leftInv f F⟪f⟫ᴰ = R.rectify $ R.≡out $
    (R.≡in $ congP (λ _ F⟪f⟫ → universalᴰ 𝟙ᴰ {xᴰ = xᴰ} .inv  F⟪f⟫ tt)
      (F .F-seq _ _ ∙ D.⟨ refl ⟩⋆⟨ F .F-id ⟩))
    ∙ sym (R.≡in $ ηᴰ 𝟙ᴰ)

  module _ {c : C .ob} {Fcᴰ Fcᴰ' : Dᴰ.ob[ F ⟅ c ⟆ ]}
    (vbp : VerticalBinProductsAt Dᴰ (Fcᴰ , Fcᴰ')) where
    private
      module Fcᴰ∧Fcᴰ' = VerticalBinProductsAtNotation vbp

    preservesVerticalBinProd : VerticalBinProductsAt (reindex Dᴰ F) (Fcᴰ , Fcᴰ')
    preservesVerticalBinProd .vertexᵛ = vbp .vertexᵛ
    preservesVerticalBinProd .elementᵛ .fst = R.reind (sym $ F .F-id) $ vbp .elementᵛ .fst
    preservesVerticalBinProd .elementᵛ .snd = R.reind (sym $ F .F-id) $ vbp .elementᵛ .snd
    preservesVerticalBinProd .universalᵛ .fst (fᴰ₁ , fᴰ₂) = fᴰ₁ Fcᴰ∧Fcᴰ'.,ᵛ fᴰ₂
    preservesVerticalBinProd .universalᵛ .snd .fst (fᴰ₁ , fᴰ₂) = ΣPathP
      ( (R.rectify $ R.≡out $
        (sym $ R.reind-filler _ _)
        ∙ (sym $ R.reind-filler _ _)
        ∙ R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
        ∙ R.reind-filler _ _
        ∙ R.≡in (Fcᴰ∧Fcᴰ'.×βᵛ₁ {fᴰ' = fᴰ₂}))
      , (R.rectify $ R.≡out $
        (sym $ R.reind-filler _ _)
        ∙ (sym $ R.reind-filler _ _)
        ∙ R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
        ∙ R.reind-filler _ _
        ∙ R.≡in (Fcᴰ∧Fcᴰ'.×βᵛ₂ {fᴰ = fᴰ₁})))
    preservesVerticalBinProd .universalᵛ .snd .snd fᴰ = R.rectify $ R.≡out $
      (R.≡in $ congP₂ (λ _ → Fcᴰ∧Fcᴰ'._,ᵛ_)
        (R.≡out $
          (sym $ R.reind-filler _ _)
          ∙ (sym $ R.reind-filler _ _)
          ∙ R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
          ∙ R.reind-filler _ _)
        (R.≡out $
          (sym $ R.reind-filler _ _)
          ∙ (sym $ R.reind-filler _ _)
          ∙ R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
          ∙ R.reind-filler _ _))
      ∙ sym (R.≡in $ Fcᴰ∧Fcᴰ'.×ηᵛ)

  hasVerticalBinProds : VerticalBinProducts Dᴰ →
    VerticalBinProducts (reindex Dᴰ F)
  hasVerticalBinProds vps Fcᴰ×Fcᴰ' =
    preservesVerticalBinProd (vps Fcᴰ×Fcᴰ')

-- module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
--   {F : Functor C D}
--   {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
--   where
--   private module Dᴰ = Categoryᴰ Dᴰ
--   module _ {c c' : C .ob} (prod : BinProduct' _ (c , c')) where
--     private module c×c' = BinProduct'Notation prod
--     module _
--       {Fcᴰ : Dᴰ.ob[ F ⟅ c ⟆ ]}
--       {Fc'ᴰ : Dᴰ.ob[ F ⟅ c' ⟆ ]}
--       (lift-π₁ : CartesianOver Dᴰ Fcᴰ (F ⟪ c×c'.π₁ ⟫))
--       (lift-π₂ : CartesianOver Dᴰ Fc'ᴰ (F ⟪ c×c'.π₂ ⟫))
--       (vbp : VerticalBinProductsAt Dᴰ (lift-π₁ .f*cᴰ' , lift-π₂ .f*cᴰ'))
--       where
--       LiftedBinProdReindex : LiftedBinProduct (reindex Dᴰ F) prod (Fcᴰ , Fc'ᴰ)
--       LiftedBinProdReindex = VerticalBinProdsAt→LiftedBinProduct
--         prod (reindex Dᴰ F)
--         (reflectsCartesianOvers Dᴰ F lift-π₁)
--         (reflectsCartesianOvers Dᴰ F lift-π₂)
--         (reindReflectsVerticalBinProd vbp)

--     module _ (Fcᴰ : Dᴰ.ob[ F ⟅ c ⟆ ]) (fib : isFibration Dᴰ) where
--       isFib→F⟪π₁⟫* : CartesianOver Dᴰ Fcᴰ (F ⟪ c×c'.π₁ ⟫)
--       isFib→F⟪π₁⟫* = CartesianLift→CartesianOver Dᴰ (fib _)
--     module _ (Fc'ᴰ : Dᴰ.ob[ F ⟅ c' ⟆ ]) (fib : isFibration Dᴰ) where
--       isFib→F⟪π₂⟫* : CartesianOver Dᴰ Fc'ᴰ (F ⟪ c×c'.π₂ ⟫)
--       isFib→F⟪π₂⟫* = CartesianLift→CartesianOver Dᴰ (fib _)

--     module _
--       {Fcᴰ : Dᴰ.ob[ F ⟅ c ⟆ ]}
--       {Fc'ᴰ : Dᴰ.ob[ F ⟅ c' ⟆ ]}
--       (lift-π₁ : CartesianOver Dᴰ Fcᴰ (F ⟪ c×c'.π₁ ⟫))
--       (lift-π₂ : CartesianOver Dᴰ Fc'ᴰ (F ⟪ c×c'.π₂ ⟫))
--       (vbps : VerticalBinProducts Dᴰ)
--       where
--       VerticalBinProds→ϕ[π₁x]∧ψ[π₂x] :
--         VerticalBinProductsAt Dᴰ (lift-π₁ .f*cᴰ' , lift-π₂ .f*cᴰ')
--       VerticalBinProds→ϕ[π₁x]∧ψ[π₂x] = vbps _

--   module _
--     (prods : BinProducts' C) where
--     private module B = BinProducts'Notation prods
--     module _
--       (lift-π₁₂ : {c c' : C .ob}
--         (Fcᴰ : Dᴰ.ob[ F ⟅ c ⟆ ])(Fc'ᴰ : Dᴰ.ob[ F ⟅ c' ⟆ ]) →
--         CartesianOver Dᴰ Fcᴰ (F ⟪ B.π₁ {a = c} {b = c'} ⟫) ×
--         CartesianOver Dᴰ Fc'ᴰ (F ⟪ B.π₂ {a = c} {b = c'} ⟫))
--       (vbp : {c c' : C .ob} (Fcᴰ : Dᴰ.ob[ F ⟅ c ⟆ ])(Fc'ᴰ : Dᴰ.ob[ F ⟅ c' ⟆ ]) →
--         VerticalBinProductsAt Dᴰ (lift-π₁₂ Fcᴰ Fc'ᴰ .fst .f*cᴰ' ,
--           lift-π₁₂ Fcᴰ Fc'ᴰ .snd .f*cᴰ'))
--       where
--       LiftedBinProductsReindex : LiftedBinProducts (reindex Dᴰ F) prods
--       LiftedBinProductsReindex (Fcᴰ , Fc'ᴰ) = LiftedBinProdReindex (prods _)
--         (lift-π₁₂ Fcᴰ Fc'ᴰ .fst)
--         (lift-π₁₂ Fcᴰ Fc'ᴰ .snd)
--         (vbp Fcᴰ Fc'ᴰ)

  module _ (prods : BinProducts' C)
    (fib : isFibration Dᴰ)
    (vbps : VerticalBinProducts Dᴰ) where
    open BinProduct'Notation
    LiftedBinProductsReindex : LiftedBinProducts (reindex Dᴰ F) prods
    LiftedBinProductsReindex dᴰ =
      Vertical→LiftedBinProduct (prods _) (reindex Dᴰ F)
        (reflectsCartesianLifts Dᴰ F (fib (dᴰ .fst) (F ⟪ π₁ (prods _) ⟫)))
        (reflectsCartesianLifts Dᴰ F (fib (dᴰ .snd) (F ⟪ π₂ (prods _) ⟫)))
        (preservesVerticalBinProd (vbps _))
