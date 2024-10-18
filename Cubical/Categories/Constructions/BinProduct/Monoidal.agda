-- Product of two categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.BinProduct.Monoidal where

import Cubical.Categories.Constructions.BinProduct as BP

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Monoidal
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors.More

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open NatTrans
open NatIso
open isIso
module _ (M : MonoidalCategory ℓC ℓC') (N : MonoidalCategory ℓD ℓD') where
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N
  _×M_ : MonoidalCategory (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
  _×M_ .MonoidalCategory.C = M.C BP.×C N.C
  _×M_ .MonoidalCategory.monstr .MonoidalStr.tenstr .TensorStr.─⊗─ =
    (M.─⊗─ ∘F (BP.Fst M.C N.C BP.×F BP.Fst M.C N.C))
    BP.,F (N.─⊗─ ∘F (BP.Snd M.C N.C BP.×F BP.Snd M.C N.C))
  _×M_ .MonoidalCategory.monstr .MonoidalStr.tenstr .TensorStr.unit =
    M.unit , N.unit
  _×M_ .MonoidalCategory.monstr .MonoidalStr.α .trans .N-ob x =
    M.α .trans ⟦ _ ⟧ , N.α .trans ⟦ _ ⟧
  _×M_ .MonoidalCategory.monstr .MonoidalStr.α .trans .N-hom f =
    ΣPathP ((M.α .trans .N-hom _) , (N.α .trans .N-hom _))
  _×M_ .MonoidalCategory.monstr .MonoidalStr.α .nIso x .inv =
    M.α⁻¹⟨ _ , _ , _ ⟩ , N.α⁻¹⟨ _ , _ , _ ⟩
  _×M_ .MonoidalCategory.monstr .MonoidalStr.α .nIso x .sec = ΣPathP ((M.α .nIso _ .sec) , (N.α .nIso _ .sec))
  _×M_ .MonoidalCategory.monstr .MonoidalStr.α .nIso x .ret = ΣPathP ((M.α .nIso _ .ret) , (N.α .nIso _ .ret))
  _×M_ .MonoidalCategory.monstr .MonoidalStr.η .trans .N-ob x = M.η⟨ _ ⟩ , N.η⟨ _ ⟩
  _×M_ .MonoidalCategory.monstr .MonoidalStr.η .trans .N-hom x = ΣPathP (M.η .trans .N-hom _ , N.η .trans .N-hom _)
  _×M_ .MonoidalCategory.monstr .MonoidalStr.η .nIso x .inv = M.η⁻¹⟨ _ ⟩ , N.η⁻¹⟨ _ ⟩
  _×M_ .MonoidalCategory.monstr .MonoidalStr.η .nIso x .sec = ΣPathP (M.η .nIso _ .sec , N.η .nIso _ .sec)
  _×M_ .MonoidalCategory.monstr .MonoidalStr.η .nIso x .ret = ΣPathP (M.η .nIso _ .ret , N.η .nIso _ .ret)
  _×M_ .MonoidalCategory.monstr .MonoidalStr.ρ .trans .N-ob x = M.ρ⟨ _ ⟩ , N.ρ⟨ _ ⟩
  _×M_ .MonoidalCategory.monstr .MonoidalStr.ρ .trans .N-hom x = ΣPathP (M.ρ .trans .N-hom _ , N.ρ .trans .N-hom _)
  _×M_ .MonoidalCategory.monstr .MonoidalStr.ρ .nIso x .inv = M.ρ⁻¹⟨ _ ⟩ , N.ρ⁻¹⟨ _ ⟩
  _×M_ .MonoidalCategory.monstr .MonoidalStr.ρ .nIso x .sec = ΣPathP (M.ρ .nIso _ .sec , N.ρ .nIso _ .sec)
  _×M_ .MonoidalCategory.monstr .MonoidalStr.ρ .nIso x .ret = ΣPathP (M.ρ .nIso _ .ret , N.ρ .nIso _ .ret)
  _×M_ .MonoidalCategory.monstr .MonoidalStr.pentagon _ _ _ _ = ΣPathP ((M.pentagon _ _ _ _ ) , (N.pentagon _ _ _ _))
  _×M_ .MonoidalCategory.monstr .MonoidalStr.triangle _ _ = ΣPathP (M.triangle _ _ , N.triangle _ _)
