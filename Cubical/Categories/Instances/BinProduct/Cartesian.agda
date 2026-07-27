-- The product of two cartesian categories is cartesian
module Cubical.Categories.Instances.BinProduct.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties

open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Instances.TotalCategory.Cartesian

open import Cubical.Categories.Displayed.Instances.Weaken.Properties

private
  variable ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level

module _
  (C : CartesianCategory ℓC ℓC')
  (D : CartesianCategory ℓD ℓD')
  where
  _×_ : CartesianCategory _ _
  _×_ = ∫C (weakenCartesianCategory C D)

pairCF :
  {B : CartesianCategory ℓB ℓB'}
  {C : CartesianCategory ℓC ℓC'}
  {D : CartesianCategory ℓD ℓD'}
  → CartesianFunctor B (C .CartesianCategory.C)
  → CartesianFunctor B (D .CartesianCategory.C)
  → CartesianFunctor B
      ((C .CartesianCategory.C) ×C (D .CartesianCategory.C))
pairCF F G .fst = F .fst ,F G .fst
pairCF F G .snd c c' Γ =
  compEquiv
    (Σ-cong-equiv
      (_ , F .snd c c' (Γ .fst))
      (λ _ → _ , G .snd c c' (Γ .snd)))
    (isoToEquiv
      (iso
        (λ z → (z .fst .fst , z .snd .fst) ,
               (z .fst .snd , z .snd .snd))
        (λ z → (z .fst .fst , z .snd .fst) ,
               (z .fst .snd , z .snd .snd))
        (λ _ → refl)
        (λ _ → refl)))
    .snd
