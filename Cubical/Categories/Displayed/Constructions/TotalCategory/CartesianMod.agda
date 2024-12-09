{-
  I couldn't make progress in Displayed.Constructions.TotalCategory.Cartesian
  due to abysmal performance issues
-}
{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.TotalCategory.CartesianMod where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function

open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Constructions.TotalCategory.Cartesian

import Cubical.Categories.Displayed.Constructions.TotalCategory as TCᴰ
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Presheaf
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓCᴰᴰ ℓCᴰᴰ' : Level

module _
  {C : CartesianCategory ℓC ℓC'}
  (Cᴰ : CartesianCategoryᴰ C ℓCᴰ ℓCᴰ')
  (Cᴰᴰ : CartesianCategoryᴰ (∫C Cᴰ) ℓCᴰᴰ ℓCᴰᴰ')
  where
  open UniversalElementᴰ
  private
    module C = CartesianCategoryNotation C
    module Cᴰ = CartesianCategoryᴰNotation Cᴰ
    module Cᴰᴰ = CartesianCategoryᴰNotation Cᴰᴰ
    module Q = HomᴰReasoning (Cᴰ .fst)
    module R = HomᴰReasoning (Cᴰᴰ .fst)
  module Lemma
    {x c c' : C.ob}
    {h : C.Hom[ x , c C.×bp c' ]}
    {xᴰ : Cᴰ.ob[ x ]}
    {cᴰ : Cᴰ.ob[ c ]}
    {c'ᴰ : Cᴰ.ob[ c' ]}
    {h₁ᴰ : Cᴰ.Hom[ h C.⋆ C.π₁ ][ xᴰ , cᴰ ]}
    {h₂ᴰ : Cᴰ.Hom[ h C.⋆ C.π₂ ][ xᴰ , c'ᴰ ]}
    {xᴰᴰ : Cᴰᴰ.ob[ x , xᴰ ]}
    {cᴰᴰ : Cᴰᴰ.ob[ c , cᴰ ]}
    {c'ᴰᴰ : Cᴰᴰ.ob[ c' , c'ᴰ ]}
    (h₁ᴰᴰ : Cᴰᴰ.Hom[ h C.⋆ C.π₁ , h₁ᴰ ][ xᴰᴰ ,  cᴰᴰ ])
    (h₂ᴰᴰ : Cᴰᴰ.Hom[ h C.⋆ C.π₂ , h₂ᴰ ][ xᴰᴰ ,  c'ᴰᴰ ])
    where
    hᴰ : Cᴰ.Hom[ h ][ xᴰ , cᴰ Cᴰ.×ᴰ c'ᴰ ]
    hᴰ = h₁ᴰ Cᴰ.,pᴰ' h₂ᴰ
    private
      h₁,h₂ᴰᴰ : Cᴰᴰ.Hom[ _ , h₁ᴰ Cᴰ.,pᴰ h₂ᴰ ][ xᴰᴰ , cᴰᴰ Cᴰᴰ.×ᴰ c'ᴰᴰ ]
      h₁,h₂ᴰᴰ = h₁ᴰᴰ Cᴰᴰ.,pᴰ h₂ᴰᴰ
      --ΣCᴰHom-η : Type (ℓ-max ℓC' ℓCᴰ')
      --ΣCᴰHom-η = Σ C.Hom[ x , c C.×bp c' ] (λ h → Cᴰ.Hom[ (h C.⋆ C.π₁) C.,p (h C.⋆ C.π₂) ][ xᴰ , cᴰ Cᴰ.×ᴰ c'ᴰ ])
      -- these don't type check without explicit type annotations
      Σhᴰ Σh₁,h₂ᴰ : Σ _ (λ h → Cᴰ.Hom[ h ][ xᴰ , cᴰ Cᴰ.×ᴰ c'ᴰ ])
      Σhᴰ = h , hᴰ
      Σh₁,h₂ᴰ = ((h C.⋆ C.π₁) C.,p (h C.⋆ C.π₂)) , (h₁ᴰ Cᴰ.,pᴰ h₂ᴰ)
    -- try to reduce  performance issue in
    -- Displayed.Constructions.TotalCategory.Cartesian
    opaque
      private
        p : Σhᴰ ≡ Σh₁,h₂ᴰ
        p = ΣPathP (C.×η ,
                  congP₂ (λ _ → Cᴰ._,pᴰ'_ )
                      (Q.rectify (Q.≡out (Q.reind-filler _  _)))
                      (Q.rectify (Q.≡out (Q.reind-filler _  _))))

      hᴰᴰ : Cᴰᴰ.Hom[ h , hᴰ ][ xᴰᴰ , cᴰᴰ Cᴰᴰ.×ᴰ c'ᴰᴰ ]
      hᴰᴰ = R.reind (sym p) h₁,h₂ᴰᴰ
      reind-filler : h₁,h₂ᴰᴰ Cᴰᴰ.≡[ sym p ] hᴰᴰ
      reind-filler = R.≡out (R.reind-filler _ _)
      -- rectify to be over an arbitrary path that isn't 700 lines long
      -- so we can make these lemmas opaque
      β₁ : hᴰᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.π₁ᴰ Cᴰᴰ.≡[ ΣPathP (refl , Cᴰ.×β₁ᴰ') ] h₁ᴰᴰ
      β₁ = R.rectify (R.≡out
          (R.≡in (congP (λ _ → Cᴰᴰ._⋆ᴰ Cᴰᴰ.π₁ᴰ) (symP reind-filler)) ∙
          R.≡in (Cᴰᴰ.×β₁ᴰ {f₁ᴰ = h₁ᴰᴰ} {f₂ᴰ = h₂ᴰᴰ})))
      β₂ : hᴰᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.π₂ᴰ Cᴰᴰ.≡[ ΣPathP (refl , Cᴰ.×β₂ᴰ') ] h₂ᴰᴰ
      β₂ = R.rectify (R.≡out
          (R.≡in (congP (λ _ → Cᴰᴰ._⋆ᴰ Cᴰᴰ.π₂ᴰ) (symP reind-filler)) ∙
          R.≡in (Cᴰᴰ.×β₂ᴰ {f₁ᴰ = h₁ᴰᴰ} {f₂ᴰ = h₂ᴰᴰ})))
      --η : {hᴰᴰ' : Cᴰᴰ.Hom[ h , hᴰ ][ xᴰᴰ , cᴰᴰ Cᴰᴰ.×ᴰ c'ᴰᴰ ]}
      --  → (h₁ᴰᴰ Cᴰᴰ.≡[ ΣPathP (refl , symP Cᴰ.×β₁ᴰ') ] hᴰᴰ' Cᴰᴰ.⋆ᴰ Cᴰᴰ.π₁ᴰ)
      --  → (h₂ᴰᴰ Cᴰᴰ.≡[ ΣPathP (refl , symP Cᴰ.×β₂ᴰ') ] hᴰᴰ' Cᴰᴰ.⋆ᴰ Cᴰᴰ.π₂ᴰ)
      --  → hᴰᴰ ≡ hᴰᴰ'
      --η pᴰᴰ qᴰᴰ = R.rectify (R.≡out (R.≡in (symP reind-filler) ∙ R.≡in (Cᴰᴰ.×η''ᴰ pᴰᴰ qᴰᴰ)))
      η' : ∀ {hᴰ'}
        → {pᴰ : h₁ᴰ ≡ hᴰ' Cᴰ.⋆ᴰ Cᴰ.π₁ᴰ}
        → {qᴰ : h₂ᴰ ≡ hᴰ' Cᴰ.⋆ᴰ Cᴰ.π₂ᴰ}
        → {hᴰ'ᴰ : Cᴰᴰ.Hom[ h , hᴰ' ][ xᴰᴰ , cᴰᴰ Cᴰᴰ.×ᴰ c'ᴰᴰ ]}
        → (h₁ᴰᴰ Cᴰᴰ.≡[ ΣPathP (refl , pᴰ) ] hᴰ'ᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.π₁ᴰ)
        → (h₂ᴰᴰ Cᴰᴰ.≡[ ΣPathP (refl , qᴰ) ] hᴰ'ᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.π₂ᴰ)
        → hᴰᴰ Cᴰᴰ.≡[ ΣPathP (refl , Cᴰ.×η''ᴰ' (sym pᴰ) (sym qᴰ)) ] hᴰ'ᴰ
      η' pᴰᴰ qᴰᴰ = R.rectify (R.≡out (R.≡in (symP reind-filler) ∙ R.≡in (Cᴰᴰ.×η''ᴰ pᴰᴰ qᴰᴰ)))
