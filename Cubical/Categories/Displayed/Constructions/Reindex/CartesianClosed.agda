{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.Reindex.CartesianClosed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.More
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Reind
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.FunctorComprehension.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Cartesian
open import Cubical.Categories.Displayed.Constructions.Reindex.Exponential
open import Cubical.Categories.Displayed.Constructions.Reindex.Fibration
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.UniversalProperties
open import Cubical.Categories.Displayed.Constructions.Reindex.UniversalQuantifier
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.ClosedV
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' ℓP ℓPᴰ ℓQ ℓQᴰ : Level

open Category
open Functor
open Functorᴰ
open NatTrans
open NatIso
open PshHom
open PshIso
open CartesianCategory

module _ {CC : CartesianCategory ℓC ℓC'} {CD : CartesianCategory ℓD ℓD'}
  {Dᴰ : ClosedCategoryⱽ CD ℓDᴰ ℓDᴰ'}
  (F : CartesianFunctor CC (CD .C)) where

  ClosedⱽReindex : ClosedCategoryⱽ CC ℓDᴰ ℓDᴰ'
  ClosedⱽReindex =
    (reindex (Dᴰ .fst) (F .fst))
    , (isFibrationReindex (Dᴰ .fst) (F .fst) (Dᴰ .snd .fst))
    , (AllLRⱽReindex (F .fst) (Dᴰ .snd .snd .fst))
    , (ExponentialsⱽReindex (F .fst) (Dᴰ .snd .snd .fst) (Dᴰ .snd .snd .snd .fst))
    , hasUniversalQuantifiersReindex (F .fst) (Dᴰ .fst) (Dᴰ .snd .fst)
      (CC .bp) (CD .bp) (F .snd) (Dᴰ .snd .snd .snd .snd)

module _ {CC : CartesianCategory ℓC ℓC'} {CD : CartesianCategory ℓD ℓD'}
  {Dᴰ : CartesianClosedCategoryⱽ CD ℓDᴰ ℓDᴰ'}
  (F : CartesianFunctor CC (CD .C)) where
  private
    module Dᴰ = CartesianClosedCategoryⱽ Dᴰ

  CCCⱽReindex : CartesianClosedCategoryⱽ CC ℓDᴰ ℓDᴰ'
  CCCⱽReindex .CartesianClosedCategoryⱽ.CCⱽ = CartesianCategoryⱽReindex Dᴰ.CCⱽ (F .fst)
  CCCⱽReindex .CartesianClosedCategoryⱽ.lrⱽ = AllLRⱽReindex (F .fst) Dᴰ.lrⱽ
  CCCⱽReindex .CartesianClosedCategoryⱽ.expⱽ = ExponentialsⱽReindex (F .fst) Dᴰ.lrⱽ Dᴰ.expⱽ
  CCCⱽReindex .CartesianClosedCategoryⱽ.forallⱽ = hasUniversalQuantifiersReindex (F .fst) Dᴰ.Cᴰ Dᴰ.cartesianLifts (CC .bp) (CD .bp) (F .snd) Dᴰ.forallⱽ
