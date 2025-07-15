{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Bifunctor.Redundant

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Presheaf.Constructions
private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'} {ℓA ℓB ℓAᴰ ℓBᴰ : Level}
  where
  private
    𝓟 = PresheafCategory C ℓA
    𝓟ᴰ = PRESHEAFᴰ Cᴰ ℓA ℓAᴰ
    𝓠 = PresheafCategory C ℓB
    𝓠ᴰ = PRESHEAFᴰ Cᴰ ℓB ℓBᴰ
    𝓡 = PresheafCategory C (ℓ-max ℓA ℓB)
    𝓡ᴰ = PRESHEAFᴰ Cᴰ (ℓ-max ℓA ℓB) (ℓ-max ℓAᴰ ℓBᴰ)

  PshProd'ᴰ : Functorᴰ PshProd' (𝓟ᴰ ×Cᴰ 𝓠ᴰ) 𝓡ᴰ
  PshProd'ᴰ = postcomposeFᴰ (C ^op) (Cᴰ ^opᴰ) ×Setsᴰ ∘Fᴰ ,Fᴰ-functorᴰ

  PshProdᴰ : Bifunctorᴰ PshProd 𝓟ᴰ 𝓠ᴰ 𝓡ᴰ
  PshProdᴰ = ParFunctorᴰToBifunctorᴰ PshProd'ᴰ
