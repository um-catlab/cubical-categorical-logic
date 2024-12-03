{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.BinProduct.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
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
open UniversalElementᴰ
open isIsoOver

module _ {C : Category ℓC ℓC'}{x₁ x₂ : C .ob}
  (prod : BinProduct' C (x₁ , x₂))
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module c×c' = BinProduct'Notation prod
    module R = HomᴰReasoning Cᴰ

  open CartesianLift
  open UniversalElementᴰ

  module _ {xᴰ₁ : Cᴰ.ob[ x₁ ]}{xᴰ₂ : Cᴰ.ob[ x₂ ]}
    (lift-π₁ : CartesianLift Cᴰ xᴰ₁ c×c'.π₁)
    (lift-π₂ : CartesianLift Cᴰ xᴰ₂ c×c'.π₂)
    (vbp : VerticalBinProductsAt Cᴰ ((lift-π₁ .f*yᴰ) , (lift-π₂ .f*yᴰ)))
    where
    open VerticalBinProductsAtNotation vbp
    Vertical→LiftedBinProduct : LiftedBinProduct Cᴰ prod (xᴰ₁ , xᴰ₂)
    Vertical→LiftedBinProduct .vertexᴰ = vert
    Vertical→LiftedBinProduct .elementᴰ .fst =
      R.reind (C .⋆IdL _) (π₁ Cᴰ.⋆ᴰ lift-π₁ .π)
    Vertical→LiftedBinProduct .elementᴰ .snd =
      R.reind (C .⋆IdL _) ((π₂ Cᴰ.⋆ᴰ lift-π₂ .π))      
    Vertical→LiftedBinProduct .universalᴰ f .inv (f₁ , f₂) (fᴰ₁ , fᴰ₂) =
      lift-π₁ .isCartesian .inv _ (R.reind (sym (c×c'.×β₁)) fᴰ₁)
      ,ᵛ lift-π₂ .isCartesian .inv _ (R.reind (sym (c×c'.×β₂)) fᴰ₂)
    -- β
    Vertical→LiftedBinProduct .universalᴰ f .rightInv g (gᴰ₁ , gᴰ₂) = ΣPathP
      ( {!!}
      , {!!})
    -- η
    Vertical→LiftedBinProduct .universalᴰ f .leftInv = {!!}
  
  --   -- internally, use more logical "book" notation to keep things straight
  --   private
  --     Γ = c
  --     Δ = c'
  --     Γ×Δ = c×c'.vert
  --     ϕ = cᴰ
  --     ψ = c'ᴰ

  --   module CartesianOverBinProduct'Notation where
  --     -- shorthand for pullback object
  --     ϕ[π₁x] : Cᴰ.ob[ Γ×Δ ]
  --     ϕ[π₁x] = lift-π₁ .f*yᴰ

  --     ψ[π₂x] : Cᴰ.ob[ Γ×Δ ]
  --     ψ[π₂x] = lift-π₂ .f*yᴰ

  --   --   -- shorthand for cartesian lift
  --   --   π₁* : Cᴰ.Hom[ c×c'.π₁ ][ ϕ[π₁x] , ϕ ]
  --   --   π₁* = lift-π₁ .π

  --   --   π₂* : Cᴰ.Hom[ c×c'.π₂ ][ ψ[π₂x] , ψ ]
  --   --   π₂* = lift-π₂ .π

  --   --   module _  {x : C .ob}{xᴰ : Cᴰ.ob[ x ]}{h : C [ x , c×c'.vert ]} where
  --   --     private
  --   --       Ξ = x
  --   --       θ = xᴰ
  --   --     module _ (fᴰ : Cᴰ.Hom[ h ⋆⟨ C ⟩ c×c'.π₁ ][ xᴰ , ϕ ]) where
  --   --       fᴰ* : ∃![ lᴰ ∈ Cᴰ.Hom[ h ][ θ , ϕ[π₁x] ] ] lᴰ Cᴰ.⋆ᴰ π₁* ≡ fᴰ
  --   --       fᴰ* = lift-π₁ .isCartesian xᴰ h fᴰ
  --   --     module _ (gᴰ : Cᴰ.Hom[ h ⋆⟨ C ⟩ c×c'.π₂ ][ xᴰ , ψ ]) where
  --   --       gᴰ* : ∃![ lᴰ ∈ Cᴰ.Hom[ h ][ xᴰ , ψ[π₂x] ] ] lᴰ Cᴰ.⋆ᴰ π₂* ≡ gᴰ
  --   --       gᴰ* = lift-π₂ .isCartesian xᴰ h gᴰ

  --   -- private module B* = CartesianOverBinProduct'Notation

  --   -- module _ (vbp : VerticalBinProductsAt Cᴰ (B*.ϕ[π₁x] , B*.ψ[π₂x])) where

  --   --   private module ϕ[π₁x]∧ψ[π₂x] = VerticalBinProductsAtNotation vbp

  --   --   private
  --   --     π₁⋆π₁* : Cᴰ.Hom[ C .id ⋆⟨ C ⟩ c×c'.π₁ ][ ϕ[π₁x]∧ψ[π₂x].vert , ϕ ]
  --   --     π₁⋆π₁* = ϕ[π₁x]∧ψ[π₂x].π₁ Cᴰ.⋆ᴰ B*.π₁*

  --   --     π₂⋆π₂* : Cᴰ.Hom[ C .id ⋆⟨ C ⟩ c×c'.π₂ ][ ϕ[π₁x]∧ψ[π₂x].vert , ψ ]
  --   --     π₂⋆π₂* = ϕ[π₁x]∧ψ[π₂x].π₂ Cᴰ.⋆ᴰ B*.π₂*

  --   --     π₁ᴰ : Cᴰ.Hom[ c×c'.π₁ ][ ϕ[π₁x]∧ψ[π₂x].vert , ϕ ]
  --   --     π₁ᴰ = R.reind (C .⋆IdL _) π₁⋆π₁*

  --   --     π₂ᴰ : Cᴰ.Hom[ c×c'.π₂ ][ ϕ[π₁x]∧ψ[π₂x].vert , ψ ]
  --   --     π₂ᴰ = R.reind (C .⋆IdL _) π₂⋆π₂*

  --   --   VerticalBinProdsAt→LiftedBinProduct : LiftedBinProduct Cᴰ prod (ϕ , ψ)
  --   --   VerticalBinProdsAt→LiftedBinProduct .vertexᴰ = ϕ[π₁x]∧ψ[π₂x].vert
  --   --   VerticalBinProdsAt→LiftedBinProduct .elementᴰ .fst = π₁ᴰ
  --   --   VerticalBinProdsAt→LiftedBinProduct .elementᴰ .snd = π₂ᴰ
  --   --   VerticalBinProdsAt→LiftedBinProduct .universalᴰ f .inv (f₁ , f₂) (fᴰ₁ , fᴰ₂) = {!!}
  --   --   VerticalBinProdsAt→LiftedBinProduct .universalᴰ f .rightInv = {!!}
  --   --   VerticalBinProdsAt→LiftedBinProduct .universalᴰ f .leftInv = {!!}
  --   --     -- {x = Ξ} {xᴰ = θ} {f = h} .equiv-proof (fᴰ , gᴰ) = uniqueExists
  --   --     --   hᴰ
  --   --     --   (≡-×
  --   --     --     (R.rectify (R.≡out (R.≡in aaa₁ ∙
  --   --     --       sym (R.⋆Assoc _ _ _) ∙
  --   --     --       R.≡in bbb₁ ∙
  --   --     --       R.≡in ccc₁ ∙
  --   --     --       R.≡in (fᴰ* .fst .snd))))
  --   --     --     (R.rectify (R.≡out (R.≡in aaa₂ ∙
  --   --     --       sym (R.⋆Assoc _ _ _) ∙
  --   --     --       R.≡in bbb₂ ∙
  --   --     --       R.≡in ccc₂ ∙
  --   --     --       R.≡in (gᴰ* .fst .snd)))))
  --   --     --   (λ _ → isSet× Cᴰ.isSetHomᴰ Cᴰ.isSetHomᴰ _ _)
  --   --     --   (λ hᴰ' p → goal hᴰ' p ∙ ϕ[π₁x]∧ψ[π₂x].η hᴰ')
  --   --     --   where
  --   --     --   fᴰ* : ∃![ fᴰ* ∈ Cᴰ.Hom[ h ][ θ , B*.ϕ[π₁x] ] ] fᴰ* Cᴰ.⋆ᴰ B*.π₁* ≡ fᴰ
  --   --     --   fᴰ* = B*.fᴰ* fᴰ

  --   --     --   gᴰ* : ∃![ gᴰ* ∈ Cᴰ.Hom[ h ][ θ , B*.ψ[π₂x] ] ] gᴰ* Cᴰ.⋆ᴰ B*.π₂* ≡ gᴰ
  --   --     --   gᴰ* = B*.gᴰ* gᴰ

  --   --     --   hᴰ : Cᴰ.Hom[ h ][ θ , ϕ[π₁x]∧ψ[π₂x].vert ]
  --   --     --   hᴰ = (fᴰ* .fst .fst) ϕ[π₁x]∧ψ[π₂x].,ᵛ (gᴰ* .fst .fst)

  --   --     --   goal : ∀ hᴰ' p → hᴰ ≡
  --   --     --     ϕ[π₁x]∧ψ[π₂x].⟨ hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁ ,
  --   --     --       hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂ ⟩
  --   --     --   goal hᴰ' p = cong₂ ϕ[π₁x]∧ψ[π₂x].⟨_,_⟩ q₁ q₂
  --   --     --     where
  --   --     --     q₁'''' : (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁) Cᴰ.⋆ᴰ B*.π₁* Cᴰ.≡[ _ ] fᴰ
  --   --     --     q₁'''' = R.≡out (R.⋆Assoc _ _ _ ∙
  --   --     --       R.⟨ refl ⟩⋆⟨ R.reind-filler _ _ ⟩ ∙
  --   --     --       R.≡in (congP (λ _ → fst) p))
  --   --     --     q₁''' :
  --   --     --       R.reind (C .⋆IdR h) (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁) Cᴰ.⋆ᴰ B*.π₁* ≡ fᴰ
  --   --     --     q₁''' = R.rectify (R.≡out (R.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ refl ⟩ ∙
  --   --     --                            R.≡in q₁''''))
  --   --     --     q₁'' : fᴰ* .fst ≡
  --   --     --       (R.reind (C .⋆IdR h) (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁) , q₁''')
  --   --     --     q₁'' = fᴰ* .snd
  --   --     --       (R.reind (C .⋆IdR h) (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁) , q₁''')
  --   --     --     q₁' : fᴰ* .fst .fst Cᴰ.≡[ _ ] hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁
  --   --     --     q₁' =
  --   --     --       R.≡out (R.≡in (congP (λ _ → fst) q₁'') ∙ sym (R.reind-filler _ _))
  --   --     --     q₁ : fᴰ* .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ ≡ hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁
  --   --     --     q₁ = R.rectify (R.≡out (R.⋆IdR _ ∙ R.≡in q₁'))

  --   --     --     q₂'''' : (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂) Cᴰ.⋆ᴰ B*.π₂* Cᴰ.≡[ _ ] gᴰ
  --   --     --     q₂'''' = R.≡out (R.⋆Assoc _ _ _ ∙
  --   --     --       R.⟨ refl ⟩⋆⟨ R.reind-filler _ _ ⟩ ∙
  --   --     --       R.≡in (congP (λ _ → snd) p))
  --   --     --     q₂''' :
  --   --     --       R.reind (C .⋆IdR h) (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂) Cᴰ.⋆ᴰ B*.π₂* ≡ gᴰ
  --   --     --     q₂''' = R.rectify (R.≡out (R.⟨ sym (R.reind-filler _ _) ⟩⋆⟨ refl ⟩ ∙
  --   --     --                      R.≡in q₂''''))
  --   --     --     q₂'' : gᴰ* .fst ≡
  --   --     --       (R.reind (C .⋆IdR h) (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂) , q₂''')
  --   --     --     q₂'' = gᴰ* .snd
  --   --     --       (R.reind (C .⋆IdR h) (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂) , q₂''')
  --   --     --     q₂' : gᴰ* .fst .fst Cᴰ.≡[ _ ] hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂
  --   --     --     q₂' =
  --   --     --       R.≡out (R.≡in (congP (λ _ → fst) q₂'') ∙ sym (R.reind-filler _ _))
  --   --     --     q₂ : gᴰ* .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ ≡ hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂
  --   --     --     q₂ = R.rectify (R.≡out (R.⋆IdR _ ∙ R.≡in q₂'))

  --   --     --   β :
  --   --     --     (hᴰ Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁ , hᴰ Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂)
  --   --     --     ≡
  --   --     --     ((fᴰ* .fst .fst) Cᴰ.⋆ᴰ Cᴰ.idᴰ , (gᴰ* .fst .fst) Cᴰ.⋆ᴰ Cᴰ.idᴰ)
  --   --     --   β = ϕ[π₁x]∧ψ[π₂x].β' (fᴰ* .fst .fst) (gᴰ* .fst .fst)

  --   --     --   aaa₁ : hᴰ Cᴰ.⋆ᴰ π₁ᴰ Cᴰ.≡[ _ ] hᴰ Cᴰ.⋆ᴰ π₁⋆π₁*
  --   --     --   aaa₁ = R.≡out (R.⟨ refl ⟩⋆⟨ sym (R.reind-filler _ _) ⟩)

  --   --     --   aaa₂ : hᴰ Cᴰ.⋆ᴰ π₂ᴰ Cᴰ.≡[ _ ] hᴰ Cᴰ.⋆ᴰ π₂⋆π₂*
  --   --     --   aaa₂ = R.≡out (R.⟨ refl ⟩⋆⟨ sym (R.reind-filler _ _) ⟩)

  --   --     --   bbb₁ : (hᴰ Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁) Cᴰ.⋆ᴰ B*.π₁* ≡
  --   --     --     (fᴰ* .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ B*.π₁*
  --   --     --   bbb₁ = congS (λ x → x .fst Cᴰ.⋆ᴰ B*.π₁*) β

  --   --     --   bbb₂ : (hᴰ Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂) Cᴰ.⋆ᴰ B*.π₂* ≡
  --   --     --     (gᴰ* .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ B*.π₂*
  --   --     --   bbb₂ = congS (λ x → x .snd Cᴰ.⋆ᴰ B*.π₂*) β

  --   --     --   ccc₁ : (fᴰ* .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ B*.π₁* Cᴰ.≡[ _ ]
  --   --     --     fᴰ* .fst .fst Cᴰ.⋆ᴰ B*.π₁*
  --   --     --   ccc₁ = congP (λ _ x → x Cᴰ.⋆ᴰ B*.π₁*) (Cᴰ.⋆IdRᴰ _)

  --   --     --   ccc₂ : (gᴰ* .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ B*.π₂* Cᴰ.≡[ _ ]
  --   --     --     gᴰ* .fst .fst Cᴰ.⋆ᴰ B*.π₂*
  --   --     --   ccc₂ = congP (λ _ x → x Cᴰ.⋆ᴰ B*.π₂*) (Cᴰ.⋆IdRᴰ _)

