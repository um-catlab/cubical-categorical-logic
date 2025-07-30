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

  PshProd' : Functor
    (PresheafCategory C ℓA ×C PresheafCategory C ℓB)
    (PresheafCategory C (ℓ-max ℓA ℓB))
  PshProd' = (postcomposeF _ ×Sets ∘F ,F-functor)

  PshProd : Bifunctor (PresheafCategory C ℓA) (PresheafCategory C ℓB)
                      (PresheafCategory C (ℓ-max ℓA ℓB))
  PshProd = ParFunctorToBifunctor PshProd'

  private
    open Category
    open Bifunctor
    open NatTrans
    -- Test to make sure we get the right definitional
    -- behavior for Bif-homL, Bif-homR
    module _ (P P' : Presheaf C ℓA)(Q Q' : Presheaf C ℓB)
             (α : PresheafCategory C ℓA [ P , P' ])
             (β : PresheafCategory C ℓB [ Q , Q' ])
             c where

      _ : PshProd .Bif-homL α Q .N-ob c ≡ λ (p , q) → α .N-ob c p , q
      _ = refl

      _ : PshProd .Bif-homR P β .N-ob c ≡ λ (p , q) → p , β .N-ob c q
      _ = refl
