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
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

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

module LiftedBinProductsNotation
         {C : Category ℓC ℓC'}
         {Cᴰ : Categoryᴰ C ℓD ℓD'}
         {bp' : BinProducts' C}
         (bpᴰ : LiftedBinProducts Cᴰ bp')
       where

  private
    module BP = BinProducts'Notation bp'
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ
  open BP
  open UniversalElementᴰ

  private
    variable
      c c' c₁ c₂ : C .ob
      d d' d₁ d₂ : Cᴰ.ob[ c ]

  _×ᴰ_ : Cᴰ.ob[ c₁ ] → Cᴰ.ob[ c₂ ] → Cᴰ.ob[ c₁ BP.× c₂ ]
  d₁ ×ᴰ d₂ = bpᴰ (d₁ , d₂) .vertexᴰ

  π₁ᴰ : Cᴰ.Hom[ π₁ ][ d₁ ×ᴰ d₂ , d₁ ]
  π₁ᴰ {d₁ = d₁ }{d₂ = d₂} = bpᴰ (d₁ , d₂) .elementᴰ .fst

  π₂ᴰ : Cᴰ.Hom[ π₂ ][ d₁ ×ᴰ d₂ , d₂ ]
  π₂ᴰ {d₁ = d₁ }{d₂ = d₂} = bpᴰ (d₁ , d₂) .elementᴰ .snd

  _,pᴰ_ : {f₁ : C [ c , c₁ ]}{f₂ : C [ c , c₂ ]}
         → Cᴰ.Hom[ f₁ ][ d , d₁ ] → Cᴰ.Hom[ f₂ ][ d , d₂ ]
         → Cᴰ.Hom[ f₁ ,p f₂ ][ d , d₁ ×ᴰ d₂ ]
  _,pᴰ_ {d₁ = d₁}{d₂ = d₂} f₁ᴰ f₂ᴰ =
    bpᴰ (d₁ , d₂) .universalᴰ .equiv-proof
      (R.reind (sym ×β₁) f₁ᴰ , R.reind (sym ×β₂) f₂ᴰ)
      .fst .fst

  module _ {f₁ : C [ c , c₁ ]}{f₂ : C [ c , c₂ ]}
           {f₁ᴰ : Cᴰ.Hom[ f₁ ][ d , d₁ ]}
           {f₂ᴰ : Cᴰ.Hom[ f₂ ][ d , d₂ ]}
         where

    private
      ,pᴰ-contr = bpᴰ (d₁ , d₂) .universalᴰ .equiv-proof
        (R.reind (sym ×β₁) f₁ᴰ , R.reind (sym ×β₂) f₂ᴰ)

    ×β₁ᴰ : ((f₁ᴰ ,pᴰ f₂ᴰ) Cᴰ.⋆ᴰ π₁ᴰ) Cᴰ.≡[ ×β₁ ] f₁ᴰ
    ×β₁ᴰ = symP (toPathP (sym (cong fst (,pᴰ-contr .fst .snd))))

    ×β₂ᴰ : ((f₁ᴰ ,pᴰ f₂ᴰ) Cᴰ.⋆ᴰ π₂ᴰ) Cᴰ.≡[ ×β₂ ] f₂ᴰ
    ×β₂ᴰ = symP (toPathP (sym (cong snd (,pᴰ-contr .fst .snd))))

  module _ {f : C [ c , c₁ BP.× c₂ ]}
           {fᴰ : Cᴰ.Hom[ f ][ d , d₁ ×ᴰ d₂ ]}
           where
    private
      ,pᴰ-contr = bpᴰ (d₁ , d₂) .universalᴰ .equiv-proof
        (R.reind (sym ×β₁) (fᴰ Cᴰ.⋆ᴰ π₁ᴰ) ,
          R.reind (sym ×β₂) (fᴰ Cᴰ.⋆ᴰ π₂ᴰ)) .snd
        ((R.reind (×η {f = f}) fᴰ) , ΣPathP
        ((R.rectify (R.≡out (R.⟨ sym (R.reind-filler ×η fᴰ) ⟩⋆⟨ refl ⟩ ∙
                             R.reind-filler (sym ×β₁) _)))
        , R.rectify (R.≡out (R.⟨ sym (R.reind-filler ×η fᴰ) ⟩⋆⟨ refl ⟩ ∙
                             R.reind-filler (sym ×β₂) _))))
    ×ηᴰ : fᴰ Cᴰ.≡[ ×η ] ((fᴰ Cᴰ.⋆ᴰ π₁ᴰ) ,pᴰ (fᴰ Cᴰ.⋆ᴰ π₂ᴰ))
    ×ηᴰ = toPathP (sym (cong fst ,pᴰ-contr))

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

