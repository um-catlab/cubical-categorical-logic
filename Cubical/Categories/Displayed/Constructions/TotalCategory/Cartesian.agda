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
open import Cubical.Categories.Displayed.Constructions.TotalCategory.CartesianMod

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
    λ hᴰᴰ' p → ΣPathP (Cᴰ.×η''ᴰ' (cong (fst ∘S fst) p) (cong (fst ∘S snd) p) , R.rectify {!Cᴰᴰ.×η''ᴰ'!})
    --λ fᴰᴰ' p → ΣPathP ((Cᴰ.×η''ᴰ' (cong (fst ∘S fst) p) (cong (fst ∘S snd) p)) , R.rectify {!!})
    --ΣPathP (Q.rectify (Q.≡out (ΣPathP (C.×η , {!!}) ∙ Q.≡in (Cᴰ.×η''ᴰ (sym (cong (fst ∘S fst) p)) (sym (cong (fst ∘S snd) p))))) , {!!})
--? ∙ (Cᴰ.×η''ᴰ {hᴰ = fᴰᴰ' .fst} ? ?)
    where
      module Lem = Lemma Cᴰ Cᴰᴰ (h₁ᴰᴰ .snd) (h₂ᴰᴰ .snd)
