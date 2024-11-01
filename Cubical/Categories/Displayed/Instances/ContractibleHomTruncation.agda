{-

  Given a displayed category Cᴰ over C, we can make the "contractible
  hom truncation" ∥ Cᴰ ∥ₕ₀ which is the free displayed category with
  contractible homs equipped with a vertical functor Cᴰ → ∥ Cᴰ ∥ₕ₀.

  Explicitly, this just replaces Cᴰ.Hom[ f ][ xᴰ , yᴰ ] with Unit. If
  Cᴰ is a bundle classifying some kind of data parameterized by C,
  then ∥ Cᴰ ∥ₕ₀ classifies "non-functorial" data parameterized by C.

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.ContractibleHomTruncation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Arrow.Base
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Constructions.TotalCategory hiding (Fst; Snd)
open import Cubical.Categories.Bifunctor.Redundant hiding (Fst; Snd)

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

module _ {C : Category ℓC ℓC'} where
  ∥_∥ₕ₀ : Categoryᴰ C ℓCᴰ ℓCᴰ' → Categoryᴰ C ℓCᴰ ℓ-zero
  ∥ Cᴰ ∥ₕ₀ = PropertyOver C Cᴰ.ob[_] where
    module Cᴰ = Categoryᴰ Cᴰ

  module _ {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
    hasContrHoms-∥ₕ₀ : hasContrHoms ∥ Cᴰ ∥ₕ₀
    hasContrHoms-∥ₕ₀ = hasContrHomsPropertyOver C _

    recV : (Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ')
      → Functorᴰ Id Cᴰ Dᴰ
      → hasContrHoms Dᴰ
      → Functorᴰ Id ∥ Cᴰ ∥ₕ₀ Dᴰ
    recV Dᴰ Fᴰ hasCHDᴰ = mkContrHomsFunctor hasCHDᴰ
      (Functorᴰ.F-obᴰ Fᴰ)
