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
      h₁,h₂ᴰᴰ : Cᴰᴰ.Hom[ (h C.⋆ C.π₁) C.,p (h C.⋆ C.π₂) , h₁ᴰ Cᴰ.,pᴰ h₂ᴰ ][ xᴰᴰ , cᴰᴰ Cᴰᴰ.×ᴰ c'ᴰᴰ ]
      h₁,h₂ᴰᴰ = h₁ᴰᴰ Cᴰᴰ.,pᴰ h₂ᴰᴰ
    -- try to reduce  performance issue in
    -- Displayed.Constructions.TotalCategory.Cartesian
    opaque
    --module _ where
      --private
        ΣCᴰHom : Type (ℓ-max ℓC' ℓCᴰ')
        ΣCᴰHom = Σ C.Hom[ x , c C.×bp c' ] (λ h → Cᴰ.Hom[ h ][ xᴰ , cᴰ Cᴰ.×ᴰ c'ᴰ ])
        ΣCᴰHom-η : Type (ℓ-max ℓC' ℓCᴰ')
        ΣCᴰHom-η = Σ C.Hom[ x , c C.×bp c' ] (λ h → Cᴰ.Hom[ (h C.⋆ C.π₁) C.,p (h C.⋆ C.π₂) ][ xᴰ , cᴰ Cᴰ.×ᴰ c'ᴰ ])
        q''' : ΣCᴰHom
        q''' = h , hᴰ
        q'' : ΣCᴰHom
        q'' = ((h C.⋆ C.π₁) C.,p (h C.⋆ C.π₂)) , (h₁ᴰ Cᴰ.,pᴰ h₂ᴰ)
        --q'''' : ΣCᴰHom-η
        --q'''' = h , (h₁ᴰ Cᴰ.,pᴰ h₂ᴰ)
        p : q''' ≡ q''
        p = ΣPathP (C.×η ,
                  congP₂ (λ _ → Cᴰ._,pᴰ'_ )
                      (Q.rectify (Q.≡out (Q.reind-filler _  _)))
                      (Q.rectify (Q.≡out (Q.reind-filler _  _))))

        hᴰᴰ : Cᴰᴰ.Hom[ h , hᴰ ][ xᴰᴰ , cᴰᴰ Cᴰᴰ.×ᴰ c'ᴰᴰ ]
        hᴰᴰ = R.reind (sym p) h₁,h₂ᴰᴰ
    opaque
        unfolding ΣCᴰHom q'' q''' p
        test : ΣCᴰHom ≡ Σ C.Hom[ x , c C.×bp c' ] (λ h → Cᴰ.Hom[ h ][ xᴰ , cᴰ Cᴰ.×ᴰ c'ᴰ ])
        test = refl
        ttt : Σ C.Hom[ x , c C.×bp c' ] (λ h → Cᴰ.Hom[ h ][ xᴰ , cᴰ Cᴰ.×ᴰ c'ᴰ ])
        ttt = h , hᴰ
        yyy : ΣCᴰHom
        yyy = h , hᴰ
        aaa : ΣCᴰHom
        aaa = q''
        bbb : Σ C.Hom[ x , c C.×bp c' ] (λ h → Cᴰ.Hom[ h ][ xᴰ , cᴰ Cᴰ.×ᴰ c'ᴰ ])
        bbb = q'''
        zzz : Σ C.Hom[ x , c C.×bp c' ] (λ h → Cᴰ.Hom[ h ][ xᴰ , cᴰ Cᴰ.×ᴰ c'ᴰ ])
        zzz = ((h C.⋆ C.π₁) C.,p (h C.⋆ C.π₂)) , (h₁ᴰ Cᴰ.,pᴰ h₂ᴰ)
        --ccc : yyy ≡ zzz
        --ccc = p
        --ddd :  ≡ yyy
        --ddd = sym p
        --testt : q''' ≡ {!ttt!}
        --testt = refl
    --  private
        A : h₁,h₂ᴰᴰ Cᴰᴰ.≡[ {!ddd!} {- sym p -} ] hᴰᴰ
        A = R.≡out (R.reind-filler _ _)
      ---- rectify to be over an arbitrary path that isn't 700 lines long
      ---- so we can make these lemmas opaque
      --β₁ : hᴰᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.π₁ᴰ Cᴰᴰ.≡[ ΣPathP (refl , Cᴰ.×β₁ᴰ') ] h₁ᴰᴰ
      --β₁ = R.rectify (R.≡out
      --    (R.≡in (congP (λ _ → Cᴰᴰ._⋆ᴰ Cᴰᴰ.π₁ᴰ) (R.≡out (sym (R.reind-filler _ _)))) ∙
      --    R.≡in (Cᴰᴰ.×β₁ᴰ {f₁ᴰ = h₁ᴰᴰ} {f₂ᴰ = h₂ᴰᴰ})))
      --β₂ : hᴰᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.π₂ᴰ Cᴰᴰ.≡[ ΣPathP (refl , Cᴰ.×β₂ᴰ') ] h₂ᴰᴰ
      --β₂ = R.rectify (R.≡out
      --    (R.≡in (congP (λ _ → Cᴰᴰ._⋆ᴰ Cᴰᴰ.π₂ᴰ) (R.≡out (sym (R.reind-filler _ _)))) ∙
      --    R.≡in (Cᴰᴰ.×β₂ᴰ {f₁ᴰ = h₁ᴰᴰ} {f₂ᴰ = h₂ᴰᴰ})))
      --η : {hᴰᴰ' : Cᴰᴰ.Hom[ h , hᴰ ][ xᴰᴰ , cᴰᴰ Cᴰᴰ.×ᴰ c'ᴰᴰ ]}
      --  → hᴰᴰ Cᴰᴰ.≡[ ΣPathP (refl , {!!}) ] hᴰᴰ'
      --η = {!R.rectify (R.≡out ?)!}
