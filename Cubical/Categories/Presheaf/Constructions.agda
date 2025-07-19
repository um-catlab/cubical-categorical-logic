{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions where

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
open import Cubical.Categories.Bifunctor

private
  variable
    ℓ ℓ' ℓA ℓB : Level

module _ {C : Category ℓ ℓ'} {ℓA ℓB : Level} where
  private
    𝓟 = PresheafCategory C ℓA
    𝓠 = PresheafCategory C ℓB
    𝓡 = PresheafCategory C (ℓ-max ℓA ℓB)

  PshProd' : Functor (𝓟 ×C 𝓠) 𝓡
  PshProd' = (postcomposeF _ ×Sets ∘F ,F-functor)

  PshProd : Bifunctor 𝓟 𝓠 𝓡
  PshProd = ParFunctorToBifunctor PshProd'

  private
    open Category
    open Bifunctor
    open NatTrans
    -- Test to make sure we get the right definitional
    -- behavior for Bif-homL, Bif-homR
    module _ (P P' : 𝓟 .ob)(Q Q' : 𝓠 .ob)
             (α : 𝓟 [ P , P' ]) (β : 𝓠 [ Q , Q' ]) c where

      _ : PshProd .Bif-homL α Q .N-ob c ≡ λ (p , q) → α .N-ob c p , q
      _ = refl

      _ : PshProd .Bif-homR P β .N-ob c ≡ λ (p , q) → p , β .N-ob c q
      _ = refl
