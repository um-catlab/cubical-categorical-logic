{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Sets.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct

open import Cubical.Foundations.Isomorphism.More

private
  variable
    ℓ ℓ' : Level

open Functor
×SetsBif : Bifunctor (SET ℓ) (SET ℓ) (SET ℓ)
×SetsBif = mkBifunctorParAx F where
  open BifunctorParAx
  F : BifunctorParAx (SET ℓ) (SET ℓ) (SET ℓ)
  F .Bif-ob A B = ⟨ A ⟩ × ⟨ B ⟩ , isSet× (A .snd) (B .snd)
  F .Bif-homL f B (x , y) = f x , y
  F .Bif-homR A g (x , y) = x , (g y)
  F .Bif-hom× f g (x , y) = (f x) , (g y)
  F .Bif-×-id = refl
  F .Bif-×-seq f f' g g' = refl
  F .Bif-L×-agree f = refl
  F .Bif-R×-agree g = refl

×Sets : Functor ((SET ℓ) ×C (SET ℓ)) (SET ℓ)
×Sets = BifunctorToParFunctor ×SetsBif

module _ {A}{B} (f : CatIso (SET ℓ) A B) a where
  open isUnivalent
  univSetβ : transport (cong fst (CatIsoToPath isUnivalentSET f)) a
             ≡ f .fst a
  univSetβ = (transportRefl _
    ∙ transportRefl _
    ∙ transportRefl _
    ∙ cong (f .fst) (transportRefl _ ∙ transportRefl _ ))
