{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where
  private
    module D = Categoryᴰ D
  BinProductᴰ : ∀ {c12} → BinProduct' C c12
              → (D.ob[ c12 .fst ] × D.ob[ c12 .snd ])
              → Type _
  BinProductᴰ = RightAdjointAtᴰ (ΔCᴰ D)

  BinProductsᴰ : BinProducts' C → Type _
  BinProductsᴰ = RightAdjointᴰ (ΔCᴰ D)

  FibBinProductsAtᴰ : ∀ {c} → (D.ob[ c ] × D.ob[ c ]) → Type _
  FibBinProductsAtᴰ = LocalRightAdjointAtᴰ (Δᴰ D)

  FibBinProductsᴰ : Type _
  FibBinProductsᴰ = LocalRightAdjointᴰ (Δᴰ D)

module BinProductᴰNotation
         {C : Category ℓC ℓC'}
         {D : Categoryᴰ C ℓD ℓD'}
         {bp' : BinProducts' C}
         (bpᴰ : BinProductsᴰ D bp')
       where

  private
    module BP = BinProducts'Notation _ bp'
    module D = Categoryᴰ D
    module R = HomᴰReasoning D
  open BP
  open UniversalElementᴰ

  private
    variable
      c c' c₁ c₂ : C .ob
      d d' d₁ d₂ : D.ob[ c ]

  _×ᴰ_ : D.ob[ c₁ ] → D.ob[ c₂ ] → D.ob[ c₁ BP.× c₂ ]
  d₁ ×ᴰ d₂ = bpᴰ (d₁ , d₂) .vertexᴰ


  π₁ᴰ : D.Hom[ π₁ ][ d₁ ×ᴰ d₂ , d₁ ]
  π₁ᴰ {d₁ = d₁ }{d₂ = d₂} = bpᴰ (d₁ , d₂) .elementᴰ .fst

  π₂ᴰ : D.Hom[ π₂ ][ d₁ ×ᴰ d₂ , d₂ ]
  π₂ᴰ {d₁ = d₁ }{d₂ = d₂} = bpᴰ (d₁ , d₂) .elementᴰ .snd

  _,pᴰ_ : {f₁ : C [ c , c₁ ]}{f₂ : C [ c , c₂ ]}
         → D.Hom[ f₁ ][ d , d₁ ] → D.Hom[ f₂ ][ d , d₂ ]
         → D.Hom[ f₁ ,p f₂ ][ d , d₁ ×ᴰ d₂ ]
  _,pᴰ_ {d₁ = d₁}{d₂ = d₂} f₁ᴰ f₂ᴰ =
    bpᴰ (d₁ , d₂) .universalᴰ .equiv-proof
      (R.reind (sym ×β₁) f₁ᴰ , R.reind (sym ×β₂) f₂ᴰ)
      .fst .fst


  module _ {f₁ : C [ c , c₁ ]}{f₂ : C [ c , c₂ ]}
           {f₁ᴰ : D.Hom[ f₁ ][ d , d₁ ]}
           {f₂ᴰ : D.Hom[ f₂ ][ d , d₂ ]}
         where

    private
      ,pᴰ-contr = bpᴰ (d₁ , d₂) .universalᴰ .equiv-proof
        (R.reind (sym ×β₁) f₁ᴰ , R.reind (sym ×β₂) f₂ᴰ)

    ×β₁ᴰ : ((f₁ᴰ ,pᴰ f₂ᴰ) D.⋆ᴰ π₁ᴰ) D.≡[ ×β₁ ] f₁ᴰ
    ×β₁ᴰ = symP (toPathP (sym (cong fst (,pᴰ-contr .fst .snd))))

    ×β₂ᴰ : ((f₁ᴰ ,pᴰ f₂ᴰ) D.⋆ᴰ π₂ᴰ) D.≡[ ×β₂ ] f₂ᴰ
    ×β₂ᴰ = symP (toPathP (sym (cong snd (,pᴰ-contr .fst .snd))))

  module _ {f : C [ c , c₁ BP.× c₂ ]}
           {fᴰ : D.Hom[ f ][ d , d₁ ×ᴰ d₂ ]}
           where
    private
      ,pᴰ-contr = bpᴰ (d₁ , d₂) .universalᴰ .equiv-proof
        (R.reind (sym ×β₁) (fᴰ D.⋆ᴰ π₁ᴰ) , R.reind (sym ×β₂) (fᴰ D.⋆ᴰ π₂ᴰ)) .snd
        ((R.reind (×η {f = f}) fᴰ) , ΣPathP
        ( R.≡[]-rectify (R.≡[]∙ _ _
          (R.≡[]⋆ _ _ (R.reind-filler-sym (sym ×η) fᴰ) (refl {x = π₁ᴰ}))
          (R.reind-filler (sym ×β₁) _))
        , R.≡[]-rectify (R.≡[]∙ _ _
          (R.≡[]⋆ _ _ (R.reind-filler-sym (sym ×η) fᴰ) (refl {x = π₂ᴰ}))
          (R.reind-filler (sym ×β₂) _))))
    ×ηᴰ : fᴰ D.≡[ ×η ] ((fᴰ D.⋆ᴰ π₁ᴰ) ,pᴰ (fᴰ D.⋆ᴰ π₂ᴰ))
    ×ηᴰ = toPathP (sym (cong fst ,pᴰ-contr))
