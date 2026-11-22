{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Reindex.CartesianClosed where

open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Reindex.Exponential
open import Cubical.Categories.Displayed.Instances.Reindex.Fibration
open import Cubical.Categories.Displayed.Instances.Reindex.UniversalQuantifier
open import Cubical.Categories.Displayed.Limits.ClosedV
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier

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
  (Dᴰ : ClosedCategoryⱽ CD ℓDᴰ ℓDᴰ')
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
  (Dᴰ : CartesianClosedCategoryⱽ CD ℓDᴰ ℓDᴰ')
  (F : CartesianFunctor CC (CD .C)) where
  private
    module Dᴰ = CartesianClosedCategoryⱽ Dᴰ

  CCCⱽReindex : CartesianClosedCategoryⱽ CC ℓDᴰ ℓDᴰ'
  CCCⱽReindex .CartesianClosedCategoryⱽ.CCⱽ = CartesianCategoryⱽReindex Dᴰ.CCⱽ (F .fst)
  CCCⱽReindex .CartesianClosedCategoryⱽ.lrⱽ = AllLRⱽReindex (F .fst) Dᴰ.lrⱽ
  CCCⱽReindex .CartesianClosedCategoryⱽ.expⱽ = ExponentialsⱽReindex (F .fst) Dᴰ.lrⱽ Dᴰ.expⱽ
  CCCⱽReindex .CartesianClosedCategoryⱽ.forallⱽ = hasUniversalQuantifiersReindex (F .fst) Dᴰ.Cᴰ Dᴰ.cartesianLifts (CC .bp) (CD .bp) (F .snd) Dᴰ.forallⱽ
    :> UniversalQuantifiers (CartesianClosedCategoryⱽ.Cᴰ CCCⱽReindex) (CC .bp) (CartesianClosedCategoryⱽ.cartesianLifts CCCⱽReindex)
