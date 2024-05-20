{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Fibration.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Adjoint.More

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'}{c c' : C .ob}
  (prod : BinProduct' C (c , c'))(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module B = BinProduct'Notation C prod
  open CartesianOver
  open UniversalElementᴰ
  module _ {cᴰ : Cᴰ.ob[ c ]}{c'ᴰ : Cᴰ.ob[ c' ]} (lift-π₁ : CartesianOver Cᴰ cᴰ B.π₁)(lift-π₂ : CartesianOver Cᴰ c'ᴰ B.π₂) where
    module BinProductsᴰNotation where
      -- internally, use more logical notation to keep things straight
      -- but expose standard Categoryᴰ interface names
      private
        Γ = c
        Δ = c'
        ϕ = cᴰ
        ψ = c'ᴰ
        Γ×Δ = B.c×c'

      -- shorthand for pullback object
      ϕ[π₁x] : Cᴰ.ob[ Γ×Δ ]
      ϕ[π₁x] = lift-π₁ .f*cᴰ'

      ψ[π₂x] : Cᴰ.ob[ Γ×Δ ]
      ψ[π₂x] = lift-π₂ .f*cᴰ'

      -- shorthand for cartesian lift
      π₁* : Cᴰ.Hom[ B.π₁ ][ ϕ[π₁x] , ϕ ]
      π₁* = lift-π₁ .π

      π₂* : Cᴰ.Hom[ B.π₂ ][ ψ[π₂x] , ψ ]
      π₂* = lift-π₂ .π

      module _  {x : C .ob}{xᴰ : Cᴰ.ob[ x ]}{h : C [ x , B.c×c' ]}
        (fᴰ : Cᴰ.Hom[ h ⋆⟨ C ⟩ B.π₁ ][ xᴰ , ϕ ]) where
        private
          Ξ = x
          θ = xᴰ
        pbfᴰ : ∃![ lᴰ ∈ Cᴰ.Hom[ h ][ θ , ϕ[π₁x] ] ] lᴰ Cᴰ.⋆ᴰ π₁* ≡ fᴰ
        pbfᴰ = lift-π₁ .isCartesian xᴰ h fᴰ
      module _  {x : C .ob}{xᴰ : Cᴰ.ob[ x ]}{h : C [ x , B.c×c' ]}
        (gᴰ : Cᴰ.Hom[ h ⋆⟨ C ⟩ B.π₂ ][ xᴰ , ψ ]) where
        private
          Ξ = x
          θ = xᴰ
        pbgᴰ : ∃![ lᴰ ∈ Cᴰ.Hom[ h ][ xᴰ , ψ[π₂x] ] ] lᴰ Cᴰ.⋆ᴰ π₂* ≡ gᴰ
        pbgᴰ = lift-π₂ .isCartesian xᴰ h gᴰ

    private module Bᴰ = BinProductsᴰNotation

    module _ (vbp : VerticalBinProductsAt Cᴰ (Bᴰ.ϕ[π₁x] , Bᴰ.ψ[π₂x])) where
      open VerticalBinProductsAtNotation vbp
      private
        Γ = c
        Δ = c'
        ϕ = cᴰ
        ψ = c'ᴰ
        Γ×Δ = B.c×c'

        ϕ[π₁x]∧ψ[π₂x] : Cᴰ.ob[ Γ×Δ ]
        ϕ[π₁x]∧ψ[π₂x] = vert-cᴰ×cᴰ'

        vert-π₁⋆π₁* : Cᴰ.Hom[ C .id ⋆⟨ C ⟩ B.π₁ ][ ϕ[π₁x]∧ψ[π₂x] , ϕ ]
        vert-π₁⋆π₁* = vert-π₁ Cᴰ.⋆ᴰ Bᴰ.π₁*

        vert-π₂⋆π₂* : Cᴰ.Hom[ C .id ⋆⟨ C ⟩ B.π₂ ][ ϕ[π₁x]∧ψ[π₂x] , ψ ]
        vert-π₂⋆π₂* = vert-π₂ Cᴰ.⋆ᴰ Bᴰ.π₂*

        rectify' : ∀{x y h}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]} → Cᴰ.Hom[ C .id ⋆⟨ C ⟩ h ][ xᴰ , yᴰ ] → Cᴰ.Hom[ h ][ xᴰ , yᴰ ]
        rectify' {h = h} {xᴰ = xᴰ} {yᴰ = yᴰ} = transport (congS (λ x → Cᴰ.Hom[ x ][ xᴰ , yᴰ ]) (C .⋆IdL h))

        rectify'' : ∀{x y h}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]} → Cᴰ.Hom[ h ⋆⟨ C ⟩ C .id ][ xᴰ , yᴰ ] → Cᴰ.Hom[ h ][ xᴰ , yᴰ ]
        rectify'' {h = h} {xᴰ = xᴰ} {yᴰ = yᴰ} = transport (congS (λ x → Cᴰ.Hom[ x ][ xᴰ , yᴰ ]) (C .⋆IdR h))

        π₁ᴰ : Cᴰ.Hom[ B.π₁ ][ ϕ[π₁x]∧ψ[π₂x] , ϕ ]
        π₁ᴰ = rectify' vert-π₁⋆π₁*

        cohere₁ : vert-π₁⋆π₁* Cᴰ.≡[ C .⋆IdL _ ] π₁ᴰ
        cohere₁ = toPathP refl

        --cohere'₁ : ∀{hᴰ} →  hᴰ Cᴰ.≡[ C .⋆IdR _ ] rectify'' hᴰ
        --cohere'₁ = toPathP refl

        π₂ᴰ : Cᴰ.Hom[ B.π₂ ][ ϕ[π₁x]∧ψ[π₂x] , ψ ]
        π₂ᴰ = rectify' vert-π₂⋆π₂*

        cohere₂ : vert-π₂⋆π₂* Cᴰ.≡[ C .⋆IdL _ ] π₂ᴰ
        cohere₂ = toPathP refl

      import Cubical.Categories.Displayed.Reasoning
      open Cubical.Categories.Displayed.Reasoning Cᴰ

      -- "the" theorem
      VerticalBinProduct→LiftedBinProduct : LiftedBinProduct Cᴰ prod (ϕ , ψ)
      VerticalBinProduct→LiftedBinProduct .vertexᴰ = ϕ[π₁x]∧ψ[π₂x] --Bᴰ.ϕ[π₁x] ×[ Γ B.× Δ ] Bᴰ.ψ[π₂x]
      VerticalBinProduct→LiftedBinProduct .elementᴰ .fst = π₁ᴰ --π₁ᴰ ϕ ψ
      VerticalBinProduct→LiftedBinProduct .elementᴰ .snd = π₂ᴰ --π₂ᴰ ϕ ψ
      VerticalBinProduct→LiftedBinProduct .universalᴰ {x = Ξ} {xᴰ = θ} {f = h} .equiv-proof (fᴰ , gᴰ) = uniqueExists
          hᴰ
          (≡-×
            (≡[]-rectify (aaa₁ [ _ ]∙[ _ ] symP (Cᴰ.⋆Assocᴰ _ _ _) [ _ ]∙[ _ ] bbb₁ [ _ ]∙[ _ ] ccc₁ [ _ ]∙[ refl ] pbfᴰ .fst .snd))
            ((≡[]-rectify (aaa₂ [ _ ]∙[ _ ] symP (Cᴰ.⋆Assocᴰ _ _ _) [ _ ]∙[ _ ] bbb₂ [ _ ]∙[ _ ] ccc₂ [ _ ]∙[ refl ] pbgᴰ .fst .snd))))
          (λ _ → isSet× Cᴰ.isSetHomᴰ Cᴰ.isSetHomᴰ _ _)
          λ hᴰ' p' → goal hᴰ' p' ∙ vert-η hᴰ'
          where
          pbfᴰ : ∃![ fᴰ* ∈ Cᴰ.Hom[ h ][ θ , Bᴰ.ϕ[π₁x] ] ] fᴰ* Cᴰ.⋆ᴰ Bᴰ.π₁* ≡ fᴰ
          pbfᴰ = Bᴰ.pbfᴰ fᴰ

          pbgᴰ : ∃![ gᴰ* ∈ Cᴰ.Hom[ h ][ θ , Bᴰ.ψ[π₂x] ] ] gᴰ* Cᴰ.⋆ᴰ Bᴰ.π₂* ≡ gᴰ
          pbgᴰ = Bᴰ.pbgᴰ gᴰ

          hᴰ : Cᴰ.Hom[ h ][ θ , ϕ[π₁x]∧ψ[π₂x] ]
          hᴰ = vert-pair' (pbfᴰ .fst .fst) (pbgᴰ .fst .fst)

          goal : ∀ hᴰ' p' → hᴰ ≡ vert-pair (hᴰ' Cᴰ.⋆ᴰ vert-π₁) (hᴰ' Cᴰ.⋆ᴰ vert-π₂)
          goal hᴰ' p' = cong₂ vert-pair one two
            where
            one'' : (hᴰ' Cᴰ.⋆ᴰ vert-π₁) Cᴰ.⋆ᴰ Bᴰ.π₁* Cᴰ.≡[ _ ] fᴰ
            one'' = Cᴰ.⋆Assocᴰ _ _ _ [ _ ]∙[ _ ] (congP (λ _ x → hᴰ' Cᴰ.⋆ᴰ x) cohere₁) [ _ ]∙[ _ ] (congP (λ _ x → x .fst) p')
            one''' : rectify'' (hᴰ' Cᴰ.⋆ᴰ vert-π₁) Cᴰ.⋆ᴰ Bᴰ.π₁* ≡ fᴰ
            one''' = ≡[]-rectify (congP (λ _ x → x Cᴰ.⋆ᴰ Bᴰ.π₁*) (symP (toPathP refl {- TODO: replace -})) [ _ ]∙[ _ ] one'')
            one'''' : pbfᴰ .fst ≡ (rectify'' (hᴰ' Cᴰ.⋆ᴰ vert-π₁) , one''')
            one'''' = pbfᴰ .snd (rectify'' (hᴰ' Cᴰ.⋆ᴰ vert-π₁) , one''')
            one' : pbfᴰ .fst .fst Cᴰ.≡[ _ ] hᴰ' Cᴰ.⋆ᴰ vert-π₁
            one' = (congP (λ _ x → x .fst) one'''') [ _ ]∙[ _ ] symP (toPathP refl) {- TODO: replace -}
            one : pbfᴰ .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ ≡ hᴰ' Cᴰ.⋆ᴰ vert-π₁
            one = ≡[]-rectify (Cᴰ.⋆IdRᴰ (pbfᴰ .fst .fst) [ _ ]∙[ _ ] one')

            two'' : (hᴰ' Cᴰ.⋆ᴰ vert-π₂) Cᴰ.⋆ᴰ Bᴰ.π₂* Cᴰ.≡[ _ ] gᴰ
            two'' = Cᴰ.⋆Assocᴰ _ _ _ [ _ ]∙[ _ ] (congP (λ _ x → hᴰ' Cᴰ.⋆ᴰ x) cohere₂) [ _ ]∙[ _ ] (congP (λ _ x → x .snd) p')
            two''' : rectify'' (hᴰ' Cᴰ.⋆ᴰ vert-π₂) Cᴰ.⋆ᴰ Bᴰ.π₂* ≡ gᴰ
            two''' = ≡[]-rectify (congP (λ _ x → x Cᴰ.⋆ᴰ Bᴰ.π₂*) (symP (toPathP refl {- TODO: replace -})) [ _ ]∙[ _ ] two'')
            two'''' : pbgᴰ .fst ≡ (rectify'' (hᴰ' Cᴰ.⋆ᴰ vert-π₂) , two''')
            two'''' = pbgᴰ .snd (rectify'' (hᴰ' Cᴰ.⋆ᴰ vert-π₂) , two''')
            two' : pbgᴰ .fst .fst Cᴰ.≡[ _ ] hᴰ' Cᴰ.⋆ᴰ vert-π₂
            two' = (congP (λ _ x → x .fst) two'''') [ _ ]∙[ _ ] symP (toPathP refl) {- TODO: replace -}
            two : pbgᴰ .fst .fst Cᴰ.⋆ᴰ Cᴰ.idᴰ ≡ hᴰ' Cᴰ.⋆ᴰ vert-π₂
            two = ≡[]-rectify (Cᴰ.⋆IdRᴰ (pbgᴰ .fst .fst) [ _ ]∙[ _ ] two')

          β :
            (hᴰ Cᴰ.⋆ᴰ vert-π₁ , hᴰ Cᴰ.⋆ᴰ vert-π₂)
            ≡
            ((pbfᴰ .fst .fst) Cᴰ.⋆ᴰ Cᴰ.idᴰ , (pbgᴰ .fst .fst) Cᴰ.⋆ᴰ Cᴰ.idᴰ)
          β = vert-β' (pbfᴰ .fst .fst) (pbgᴰ .fst .fst)

          aaa₁ : (hᴰ Cᴰ.⋆ᴰ π₁ᴰ Cᴰ.≡[ _ ] hᴰ Cᴰ.⋆ᴰ vert-π₁⋆π₁*)
          aaa₁ = congP (λ _ x → hᴰ Cᴰ.⋆ᴰ x) (symP cohere₁)

          aaa₂ : (hᴰ Cᴰ.⋆ᴰ π₂ᴰ Cᴰ.≡[ _ ] hᴰ Cᴰ.⋆ᴰ vert-π₂⋆π₂*)
          aaa₂ = congP (λ _ x → hᴰ Cᴰ.⋆ᴰ x) (symP cohere₂)

          bbb₁ : (hᴰ Cᴰ.⋆ᴰ vert-π₁) Cᴰ.⋆ᴰ Bᴰ.π₁* ≡ ((pbfᴰ .fst .fst) Cᴰ.⋆ᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ Bᴰ.π₁*
          bbb₁ = congS (λ x → (x .fst) Cᴰ.⋆ᴰ Bᴰ.π₁*) β

          bbb₂ : (hᴰ Cᴰ.⋆ᴰ vert-π₂) Cᴰ.⋆ᴰ Bᴰ.π₂* ≡ ((pbgᴰ .fst .fst) Cᴰ.⋆ᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ Bᴰ.π₂*
          bbb₂ = congS (λ x → (x .snd) Cᴰ.⋆ᴰ Bᴰ.π₂*) β

          ccc₁ : ((pbfᴰ .fst .fst) Cᴰ.⋆ᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ Bᴰ.π₁* Cᴰ.≡[ _ ] (pbfᴰ .fst .fst) Cᴰ.⋆ᴰ Bᴰ.π₁*
          ccc₁ = congP (λ _ x → x Cᴰ.⋆ᴰ Bᴰ.π₁*) (Cᴰ.⋆IdRᴰ _)

          ccc₂ : ((pbgᴰ .fst .fst) Cᴰ.⋆ᴰ Cᴰ.idᴰ) Cᴰ.⋆ᴰ Bᴰ.π₂* Cᴰ.≡[ _ ] (pbgᴰ .fst .fst) Cᴰ.⋆ᴰ Bᴰ.π₂*
          ccc₂ = congP (λ _ x → x Cᴰ.⋆ᴰ Bᴰ.π₂*) (Cᴰ.⋆IdRᴰ _)
