{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
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
import Cubical.Categories.Displayed.Reasoning

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open UniversalElementᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓD ℓD') where
  private module Cᴰ = Categoryᴰ Cᴰ
  LiftedBinProduct : ∀ {c12} → BinProduct' C c12
              → (Cᴰ.ob[ c12 .fst ] × Cᴰ.ob[ c12 .snd ])
              → Type _
  LiftedBinProduct = RightAdjointAtᴰ (ΔCᴰ Cᴰ)

  LiftedBinProducts : BinProducts' C → Type _
  LiftedBinProducts = RightAdjointᴰ (ΔCᴰ Cᴰ)

  VerticalBinProductsAt : ∀ {c} → (Cᴰ.ob[ c ] × Cᴰ.ob[ c ]) → Type _
  VerticalBinProductsAt = VerticalRightAdjointAtᴰ (Δᴰ Cᴰ)

  VerticalBinProducts : Type _
  VerticalBinProducts = VerticalRightAdjointᴰ (Δᴰ Cᴰ)

module _ {C  : Category ℓC ℓC'}{c : C .ob}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private module Cᴰ = Categoryᴰ Cᴰ
  -- meant to be used as `module cᴰ∧cᴰ' = VerticalBinProductsAtNotation vbp`
  module VerticalBinProductsAtNotation {cᴰ cᴰ' : Cᴰ.ob[ c ]}
    (vbp : VerticalBinProductsAt Cᴰ (cᴰ , cᴰ')) where

    vert : Cᴰ.ob[ c ]
    vert = vbp .vertexᴰ

    -- shorthand for terminal vertical cone
    π₁₂ :
      Cᴰ.Hom[ C .id ][ vert , cᴰ ] × Cᴰ.Hom[ C .id ][ vert , cᴰ' ]
    π₁₂ = vbp .elementᴰ
    π₁ = π₁₂ .fst
    π₂ = π₁₂ .snd

    module _ {x : C .ob}{xᴰ : Cᴰ.ob[ x ]}{f : C [ x , c ]} where
      ⟨_,_⟩ : Cᴰ.Hom[ f ⋆⟨ C ⟩ C .id ][ xᴰ , cᴰ ] →
        Cᴰ.Hom[ f ⋆⟨ C ⟩ C .id ][ xᴰ , cᴰ' ] →
        Cᴰ.Hom[ f ][ xᴰ , vert ]
      ⟨ fᴰ , fᴰ' ⟩ = invIsEq (vbp .universalᴰ) (fᴰ , fᴰ')

      ⟨_,_⟩' : Cᴰ.Hom[ f ][ xᴰ , cᴰ ] →
        Cᴰ.Hom[ f ][ xᴰ , cᴰ' ] →
        Cᴰ.Hom[ f ][ xᴰ , vert ]
      ⟨ fᴰ , fᴰ' ⟩' = ⟨ fᴰ Cᴰ.⋆ᴰ Cᴰ.idᴰ , fᴰ' Cᴰ.⋆ᴰ Cᴰ.idᴰ ⟩

      β : (fᴰ : Cᴰ.Hom[ f ⋆⟨ C ⟩ C .id ][ xᴰ , cᴰ ]) →
        (fᴰ' : Cᴰ.Hom[ f ⋆⟨ C ⟩ C .id ][ xᴰ , cᴰ' ]) →
        (⟨ fᴰ , fᴰ' ⟩ Cᴰ.⋆ᴰ π₁ , ⟨ fᴰ , fᴰ' ⟩ Cᴰ.⋆ᴰ π₂) ≡
        (fᴰ , fᴰ')
      β fᴰ fᴰ' = secIsEq (vbp .universalᴰ) (fᴰ , fᴰ')

      β' : (fᴰ : Cᴰ.Hom[ f ][ xᴰ , cᴰ ]) →
        (fᴰ' : Cᴰ.Hom[ f ][ xᴰ , cᴰ' ]) →
        (⟨ fᴰ , fᴰ' ⟩' Cᴰ.⋆ᴰ π₁ , ⟨ fᴰ , fᴰ' ⟩' Cᴰ.⋆ᴰ π₂) ≡
        (fᴰ Cᴰ.⋆ᴰ Cᴰ.idᴰ , fᴰ' Cᴰ.⋆ᴰ Cᴰ.idᴰ)
      β' fᴰ fᴰ' = β (fᴰ Cᴰ.⋆ᴰ Cᴰ.idᴰ) (fᴰ' Cᴰ.⋆ᴰ Cᴰ.idᴰ)

      η : (fᴰ'' : Cᴰ.Hom[ f ][ xᴰ , vert ]) →
         ⟨ fᴰ'' Cᴰ.⋆ᴰ π₁ , fᴰ'' Cᴰ.⋆ᴰ π₂ ⟩ ≡ fᴰ''
      η fᴰ'' = retIsEq (vbp .universalᴰ) fᴰ''

module _ {C : Category ℓC ℓC'}{c c' : C .ob}
  (prod : BinProduct' C (c , c'))(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  open CartesianOver
  open UniversalElementᴰ
  open Cubical.Categories.Displayed.Reasoning Cᴰ

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module c×c' = BinProduct'Notation prod

  module _ {cᴰ : Cᴰ.ob[ c ]}{c'ᴰ : Cᴰ.ob[ c' ]}
    (lift-π₁ : CartesianOver Cᴰ cᴰ c×c'.π₁)
    (lift-π₂ : CartesianOver Cᴰ c'ᴰ c×c'.π₂) where
    -- internally, use more logical "book" notation to keep things straight
    private
      Γ = c
      Δ = c'
      Γ×Δ = c×c'.vert
      ϕ = cᴰ
      ψ = c'ᴰ

    module CartesianOverBinProduct'Notation where
      -- shorthand for pullback object
      ϕ[π₁x] : Cᴰ.ob[ Γ×Δ ]
      ϕ[π₁x] = lift-π₁ .f*cᴰ'

      ψ[π₂x] : Cᴰ.ob[ Γ×Δ ]
      ψ[π₂x] = lift-π₂ .f*cᴰ'

      -- shorthand for cartesian lift
      π₁* : Cᴰ.Hom[ c×c'.π₁ ][ ϕ[π₁x] , ϕ ]
      π₁* = lift-π₁ .π

      π₂* : Cᴰ.Hom[ c×c'.π₂ ][ ψ[π₂x] , ψ ]
      π₂* = lift-π₂ .π

      module _  {x : C .ob}{xᴰ : Cᴰ.ob[ x ]}{h : C [ x , c×c'.vert ]} where
        private
          Ξ = x
          θ = xᴰ
        module _ (fᴰ : Cᴰ.Hom[ h ⋆⟨ C ⟩ c×c'.π₁ ][ xᴰ , ϕ ]) where
          fᴰ* : ∃![ lᴰ ∈ Cᴰ.Hom[ h ][ θ , ϕ[π₁x] ] ] lᴰ Cᴰ.⋆ᴰ π₁* ≡ fᴰ
          fᴰ* = lift-π₁ .isCartesian xᴰ h fᴰ
        module _ (gᴰ : Cᴰ.Hom[ h ⋆⟨ C ⟩ c×c'.π₂ ][ xᴰ , ψ ]) where
          gᴰ* : ∃![ lᴰ ∈ Cᴰ.Hom[ h ][ xᴰ , ψ[π₂x] ] ] lᴰ Cᴰ.⋆ᴰ π₂* ≡ gᴰ
          gᴰ* = lift-π₂ .isCartesian xᴰ h gᴰ

    private module B* = CartesianOverBinProduct'Notation

    module _ (vbp : VerticalBinProductsAt Cᴰ (B*.ϕ[π₁x] , B*.ψ[π₂x])) where

      private module ϕ[π₁x]∧ψ[π₂x] = VerticalBinProductsAtNotation vbp

      private
        π₁⋆π₁* : Cᴰ.Hom[ C .id ⋆⟨ C ⟩ c×c'.π₁ ][ ϕ[π₁x]∧ψ[π₂x].vert , ϕ ]
        π₁⋆π₁* = ϕ[π₁x]∧ψ[π₂x].π₁ Cᴰ.⋆ᴰ B*.π₁*

        π₂⋆π₂* : Cᴰ.Hom[ C .id ⋆⟨ C ⟩ c×c'.π₂ ][ ϕ[π₁x]∧ψ[π₂x].vert , ψ ]
        π₂⋆π₂* = ϕ[π₁x]∧ψ[π₂x].π₂ Cᴰ.⋆ᴰ B*.π₂*

        π₁ᴰ : Cᴰ.Hom[ c×c'.π₁ ][ ϕ[π₁x]∧ψ[π₂x].vert , ϕ ]
        π₁ᴰ = reind (C .⋆IdL _) π₁⋆π₁*

        π₂ᴰ : Cᴰ.Hom[ c×c'.π₂ ][ ϕ[π₁x]∧ψ[π₂x].vert , ψ ]
        π₂ᴰ = reind (C .⋆IdL _) π₂⋆π₂*

      VerticalBinProdsAt→LiftedBinProduct : LiftedBinProduct Cᴰ prod (ϕ , ψ)
      VerticalBinProdsAt→LiftedBinProduct .vertexᴰ = ϕ[π₁x]∧ψ[π₂x].vert
      VerticalBinProdsAt→LiftedBinProduct .elementᴰ .fst = π₁ᴰ
      VerticalBinProdsAt→LiftedBinProduct .elementᴰ .snd = π₂ᴰ
      VerticalBinProdsAt→LiftedBinProduct .universalᴰ
        {x = Ξ} {xᴰ = θ} {f = h} .equiv-proof (fᴰ , gᴰ) = uniqueExists
          hᴰ
          (≡-×
            (≡[]-rectify (aaa₁ [ _ ]∙[ _ ]
              symP (Cᴰ.⋆Assocᴰ _ _ _) [ _ ]∙[ _ ]
              bbb₁ [ _ ]∙[ _ ]
              ccc₁ [ _ ]∙[ refl ]
              fᴰ* .fst .snd))
            (≡[]-rectify (aaa₂ [ _ ]∙[ _ ]
              symP (Cᴰ.⋆Assocᴰ _ _ _) [ _ ]∙[ _ ]
              bbb₂ [ _ ]∙[ _ ]
              ccc₂ [ _ ]∙[ refl ]
              gᴰ* .fst .snd)))
          (λ _ → isSet× Cᴰ.isSetHomᴰ Cᴰ.isSetHomᴰ _ _)
          (λ hᴰ' p → goal hᴰ' p ∙ ϕ[π₁x]∧ψ[π₂x].η hᴰ')
          where
          fᴰ* : ∃![ fᴰ* ∈ Cᴰ.Hom[ h ][ θ , B*.ϕ[π₁x] ] ] fᴰ* Cᴰ.⋆ᴰ B*.π₁* ≡ fᴰ
          fᴰ* = B*.fᴰ* fᴰ

          gᴰ* : ∃![ gᴰ* ∈ Cᴰ.Hom[ h ][ θ , B*.ψ[π₂x] ] ] gᴰ* Cᴰ.⋆ᴰ B*.π₂* ≡ gᴰ
          gᴰ* = B*.gᴰ* gᴰ

          hᴰ : Cᴰ.Hom[ h ][ θ , ϕ[π₁x]∧ψ[π₂x].vert ]
          hᴰ = ϕ[π₁x]∧ψ[π₂x].⟨ fᴰ* .fst .fst , gᴰ* .fst .fst ⟩'

          goal : ∀ hᴰ' p → hᴰ ≡
            ϕ[π₁x]∧ψ[π₂x].⟨ hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁ ,
              hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂ ⟩
          goal hᴰ' p = cong₂ ϕ[π₁x]∧ψ[π₂x].⟨_,_⟩ q₁ q₂
            where
            q₁'''' : (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁) Cᴰ.⋆ᴰ B*.π₁* Cᴰ.≡[ _ ] fᴰ
            q₁'''' = Cᴰ.⋆Assocᴰ _ _ _ [ _ ]∙[ _ ]
              congP (λ _ x → hᴰ' Cᴰ.⋆ᴰ x) (reind-filler _ _) [ _ ]∙[ _ ]
              congP (λ _ → fst) p
            q₁''' :
              reind (C .⋆IdR h) (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁) Cᴰ.⋆ᴰ B*.π₁* ≡ fᴰ
            q₁''' = ≡[]-rectify
              (congP (λ _ x → x Cᴰ.⋆ᴰ B*.π₁*) (reind-filler-sym _ _)
              [ _ ]∙[ _ ] q₁'''')
            q₁'' : fᴰ* .fst ≡
              (reind (C .⋆IdR h) (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁) , q₁''')
            q₁'' = fᴰ* .snd
              (reind (C .⋆IdR h) (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁) , q₁''')
            q₁' : fᴰ* .fst .fst Cᴰ.≡[ _ ] hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁
            q₁' = congP (λ _ → fst) q₁'' [ _ ]∙[ _ ] reind-filler-sym _ _
            q₁ : fᴰ* .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ ≡ hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁
            q₁ = ≡[]-rectify (Cᴰ.⋆IdRᴰ (fᴰ* .fst .fst) [ _ ]∙[ _ ] q₁')

            q₂'''' : (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂) Cᴰ.⋆ᴰ B*.π₂* Cᴰ.≡[ _ ] gᴰ
            q₂'''' = Cᴰ.⋆Assocᴰ _ _ _ [ _ ]∙[ _ ]
              (congP (λ _ x → hᴰ' Cᴰ.⋆ᴰ x) (reind-filler _ _)) [ _ ]∙[ _ ]
              (congP (λ _ → snd) p)
            q₂''' :
              reind (C .⋆IdR h) (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂) Cᴰ.⋆ᴰ B*.π₂* ≡ gᴰ
            q₂''' = ≡[]-rectify (congP (λ _ x → x Cᴰ.⋆ᴰ B*.π₂*)
              (reind-filler-sym _ _) [ _ ]∙[ _ ] q₂'''')
            q₂'' : gᴰ* .fst ≡
              (reind (C .⋆IdR h) (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂) , q₂''')
            q₂'' = gᴰ* .snd
              (reind (C .⋆IdR h) (hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂) , q₂''')
            q₂' : gᴰ* .fst .fst Cᴰ.≡[ _ ] hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂
            q₂' = congP (λ _ → fst) q₂'' [ _ ]∙[ _ ] reind-filler-sym _ _
            q₂ : gᴰ* .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ ≡ hᴰ' Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂
            q₂ = ≡[]-rectify (Cᴰ.⋆IdRᴰ (gᴰ* .fst .fst) [ _ ]∙[ _ ] q₂')

          β :
            (hᴰ Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁ , hᴰ Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂)
            ≡
            ((fᴰ* .fst .fst) Cᴰ.⋆ᴰ Cᴰ.idᴰ , (gᴰ* .fst .fst) Cᴰ.⋆ᴰ Cᴰ.idᴰ)
          β = ϕ[π₁x]∧ψ[π₂x].β' (fᴰ* .fst .fst) (gᴰ* .fst .fst)

          aaa₁ : hᴰ Cᴰ.⋆ᴰ π₁ᴰ Cᴰ.≡[ _ ] hᴰ Cᴰ.⋆ᴰ π₁⋆π₁*
          aaa₁ = congP (λ _ x → hᴰ Cᴰ.⋆ᴰ x) (reind-filler-sym _ _)

          aaa₂ : hᴰ Cᴰ.⋆ᴰ π₂ᴰ Cᴰ.≡[ _ ] hᴰ Cᴰ.⋆ᴰ π₂⋆π₂*
          aaa₂ = congP (λ _ x → hᴰ Cᴰ.⋆ᴰ x) (reind-filler-sym _ _)

          bbb₁ : (hᴰ Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₁) Cᴰ.⋆ᴰ B*.π₁* ≡
            (fᴰ* .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ B*.π₁*
          bbb₁ = congS (λ x → x .fst Cᴰ.⋆ᴰ B*.π₁*) β

          bbb₂ : (hᴰ Cᴰ.⋆ᴰ ϕ[π₁x]∧ψ[π₂x].π₂) Cᴰ.⋆ᴰ B*.π₂* ≡
            (gᴰ* .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ B*.π₂*
          bbb₂ = congS (λ x → x .snd Cᴰ.⋆ᴰ B*.π₂*) β

          ccc₁ : (fᴰ* .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ B*.π₁* Cᴰ.≡[ _ ]
            fᴰ* .fst .fst Cᴰ.⋆ᴰ B*.π₁*
          ccc₁ = congP (λ _ x → x Cᴰ.⋆ᴰ B*.π₁*) (Cᴰ.⋆IdRᴰ _)

          ccc₂ : (gᴰ* .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ B*.π₂* Cᴰ.≡[ _ ]
            gᴰ* .fst .fst Cᴰ.⋆ᴰ B*.π₂*
          ccc₂ = congP (λ _ x → x Cᴰ.⋆ᴰ B*.π₂*) (Cᴰ.⋆IdRᴰ _)
