
module Cubical.Categories.Instances.Sets.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Presheaf

private
  variable
    ℓ ℓ' : Level

open Functor
×SetsBif : Bifunctor (SET ℓ) (SET ℓ') (SET (ℓ-max ℓ ℓ'))
×SetsBif = mkBifunctorParAx F where
  open BifunctorParAx
  F : BifunctorParAx (SET _) (SET _) (SET _)
  F .Bif-ob A B .fst = ⟨ A ⟩ × ⟨ B ⟩
  F .Bif-ob A B .snd = isSet× (A .snd) (B .snd)
  F .Bif-homL = λ f d z → f (z .fst) , z .snd
  F .Bif-homR = λ c g z → z .fst , g (z .snd)
  F .Bif-hom× = λ f g z → f (z .fst) , g (z .snd)
  F .Bif-×-id = refl
  F .Bif-×-seq f f' g g' = refl
  F .Bif-L×-agree f = refl
  F .Bif-R×-agree g = refl

×Sets : Functor (SET ℓ ×C SET ℓ') (SET (ℓ-max ℓ ℓ'))
×Sets = BifunctorToParFunctor ×SetsBif
