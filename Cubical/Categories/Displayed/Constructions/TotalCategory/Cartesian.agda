{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.TotalCategory.Cartesian where

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
    module R = HomᴰReasoning (Cᴰ .fst)
    module Rᴰ = HomᴰReasoning (Cᴰᴰ .fst)
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
                      (R.rectify (R.≡out (R.reind-filler _  _)))
                      (R.rectify (R.≡out (R.reind-filler _  _))))

      hᴰᴰ : Cᴰᴰ.Hom[ h , hᴰ ][ xᴰᴰ , cᴰᴰ Cᴰᴰ.×ᴰ c'ᴰᴰ ]
      hᴰᴰ = Rᴰ.reind (sym p) h₁,h₂ᴰᴰ
      -- rectify to be over an arbitrary path that isn't 700 lines long
      -- so we can make these lemmas opaque
      β₁ : hᴰᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.π₁ᴰ Cᴰᴰ.≡[ ΣPathP (refl , Cᴰ.×β₁ᴰ') ] h₁ᴰᴰ
      β₁ = Rᴰ.rectify (Rᴰ.≡out
          (Rᴰ.⟨ sym (Rᴰ.reind-filler _ _) ⟩⋆⟨ refl ⟩ ∙
          Rᴰ.≡in (Cᴰᴰ.×β₁ᴰ {f₁ᴰ = h₁ᴰᴰ} {f₂ᴰ = h₂ᴰᴰ})))
      β₂ : hᴰᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.π₂ᴰ Cᴰᴰ.≡[ ΣPathP (refl , Cᴰ.×β₂ᴰ') ] h₂ᴰᴰ
      β₂ = Rᴰ.rectify (Rᴰ.≡out
          (Rᴰ.⟨ sym (Rᴰ.reind-filler _ _) ⟩⋆⟨ refl ⟩ ∙
          Rᴰ.≡in (Cᴰᴰ.×β₂ᴰ {f₁ᴰ = h₁ᴰᴰ} {f₂ᴰ = h₂ᴰᴰ})))
      η' : ∀ {hᴰ'}
        → {pᴰ : h₁ᴰ ≡ hᴰ' Cᴰ.⋆ᴰ Cᴰ.π₁ᴰ}
        → {qᴰ : h₂ᴰ ≡ hᴰ' Cᴰ.⋆ᴰ Cᴰ.π₂ᴰ}
        → {hᴰ'ᴰ : Cᴰᴰ.Hom[ h , hᴰ' ][ xᴰᴰ , cᴰᴰ Cᴰᴰ.×ᴰ c'ᴰᴰ ]}
        → (h₁ᴰᴰ Cᴰᴰ.≡[ ΣPathP (refl , pᴰ) ] hᴰ'ᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.π₁ᴰ)
        → (h₂ᴰᴰ Cᴰᴰ.≡[ ΣPathP (refl , qᴰ) ] hᴰ'ᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.π₂ᴰ)
        → hᴰᴰ Cᴰᴰ.≡[ ΣPathP (refl , Cᴰ.×η''ᴰ' (sym pᴰ) (sym qᴰ)) ] hᴰ'ᴰ
      η' pᴰᴰ qᴰᴰ = Rᴰ.rectify (Rᴰ.≡out (sym (Rᴰ.reind-filler _ _) ∙ Rᴰ.≡in (Cᴰᴰ.×η''ᴰ pᴰᴰ qᴰᴰ)))
  ∫Cᴰ : CartesianCategoryᴰ C (ℓ-max ℓCᴰ ℓCᴰᴰ) (ℓ-max ℓCᴰ' ℓCᴰᴰ')
  ∫Cᴰ .fst = TCᴰ.∫Cᴰ (Cᴰ .fst) (Cᴰᴰ .fst)
  ∫Cᴰ .snd .fst .vertexᴰ = _ , Cᴰᴰ.𝟙ᴰ
  ∫Cᴰ .snd .fst .elementᴰ = _
  ∫Cᴰ .snd .fst .universalᴰ .equiv-proof _ = uniqueExists
    (Cᴰ.!tᴰ' , Cᴰᴰ.!tᴰ')
    refl
    (λ _ _ _ → refl)
    λ _ _ → ΣPathP (Cᴰ.𝟙η'ᴰ _ _ , Cᴰᴰ.𝟙η'ᴰ _ _)
  ∫Cᴰ .snd .snd (cᴰᴰ , c'ᴰᴰ) .vertexᴰ = _ , (cᴰᴰ .snd Cᴰᴰ.×ᴰ c'ᴰᴰ .snd)
  ∫Cᴰ .snd .snd (cᴰᴰ , c'ᴰᴰ) .elementᴰ = (_ , Cᴰᴰ.π₁ᴰ) , (_ , Cᴰᴰ.π₂ᴰ)
  ∫Cᴰ .snd .snd (cᴰᴰ , c'ᴰᴰ) .universalᴰ .equiv-proof (h₁ᴰᴰ , h₂ᴰᴰ) = uniqueExists
    (Lem.hᴰ , Lem.hᴰᴰ)
    (≡-×
      (ΣPathP (_ , Lem.β₁))
      (ΣPathP (_ , Lem.β₂)))
    (λ _ → isSet× (isSetΣ Cᴰ.isSetHomᴰ (λ _ → Cᴰᴰ.isSetHomᴰ)) (isSetΣ Cᴰ.isSetHomᴰ (λ _ → Cᴰᴰ.isSetHomᴰ)) _ _)
    λ _ p → ΣPathP (Cᴰ.×η''ᴰ' (cong (fst ∘S fst) p) (cong (fst ∘S snd) p) ,
      Lem.η' (symP (cong (snd ∘ fst) p)) (symP (cong (snd ∘ snd) p)))
    where
    module Lem = Lemma (h₁ᴰᴰ .snd) (h₂ᴰᴰ .snd)
