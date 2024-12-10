{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
{-
  Weaken a cartesian category to be a displayed cartesian category.
-}
module Cubical.Categories.Displayed.Constructions.Weaken.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Limits.Cartesian
import Cubical.Categories.Displayed.Constructions.Weaken.Base as Weaken

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ (C : CartesianCategory ℓC ℓC') (D : CartesianCategory ℓD ℓD') where
  open UniversalElementᴰ
  private
    module C = CartesianCategoryNotation C
    module D = CartesianCategoryNotation D
  -- TODO: this is Cubical/Categories/Displayed/Constructions/Weaken/Properties.agda
  -- in PR #117
  weaken : CartesianCategoryᴰ C ℓD ℓD'
  weaken .fst = Weaken.weaken (C .fst) (D .fst)
  weaken .snd .fst .vertexᴰ = D.𝟙
  weaken .snd .fst .elementᴰ = _
  weaken .snd .fst .universalᴰ .equiv-proof _ = uniqueExists
    D.!t
    refl
    (λ _ _ _ → refl)
    λ _ _ → D.𝟙η'
  weaken .snd .snd (d , d') .vertexᴰ = d D.×bp d'
  weaken .snd .snd (d , d') .elementᴰ = D.π₁ , D.π₂
  weaken .snd .snd (d , d') .universalᴰ .equiv-proof (f , g) = uniqueExists
    (f D.,p g)
    (≡-× D.×β₁ D.×β₂)
    (λ _ → isSet× D.isSetHom D.isSetHom _ _)
    λ _ p → D.×η'' (sym (cong fst p)) (sym (cong snd p))
