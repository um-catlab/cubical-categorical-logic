{-

  Simple categories with families are one approach to modeling the
  judgmental structure of simply typed lambda calculus.

  Definition 9 in https://arxiv.org/abs/1904.00827

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.WithFamilies.Simple.Instances.Democratic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Presheaf.CartesianLift
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Displayed

open Category
open Categoryᴰ

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ (CC : CartesianCategory ℓC ℓC') where
  private
    module CC = CartesianCategory CC
  CartesianCategory→SCwF : SCwF ℓC ℓC' ℓC ℓC'
  CartesianCategory→SCwF .fst = CC.C
  CartesianCategory→SCwF .snd .fst = CC.C .ob
  CartesianCategory→SCwF .snd .snd .fst = CC.C [-,_]
  CartesianCategory→SCwF .snd .snd .snd .fst = CC.term
  CartesianCategory→SCwF .snd .snd .snd .snd x y = CC.bp (x , y)

module _
  {C : CartesianCategory ℓC ℓC'}
  (Cᴰ : CartesianCategoryᴰ C ℓCᴰ ℓCᴰ')
  where
  private
    module Cᴰ = CartesianCategoryᴰ Cᴰ
  CartesianCategoryᴰ→SCwFᴰ : SCwFᴰ (CartesianCategory→SCwF C) ℓCᴰ ℓCᴰ' ℓCᴰ ℓCᴰ'
  CartesianCategoryᴰ→SCwFᴰ .fst = Cᴰ.Cᴰ
  CartesianCategoryᴰ→SCwFᴰ .snd .fst = Cᴰ.Cᴰ.ob[_]
  CartesianCategoryᴰ→SCwFᴰ .snd .snd .fst = Cᴰ.Cᴰ [-][-,_]
  CartesianCategoryᴰ→SCwFᴰ .snd .snd .snd .fst = Cᴰ.termᴰ
  CartesianCategoryᴰ→SCwFᴰ .snd .snd .snd .snd Γᴰ Aᴰ = Cᴰ.bpᴰ (Γᴰ , Aᴰ)

module _
  {C : CartesianCategory ℓC ℓC'}
  (Cⱽ : CartesianCategoryⱽ (C .CartesianCategory.C) ℓCᴰ ℓCᴰ')
  where
  private
    module Cⱽ = CartesianCategoryⱽ Cⱽ
  CartesianCategoryⱽ→SCwFⱽ : SCwFⱽ (CartesianCategory→SCwF C) ℓCᴰ ℓCᴰ' ℓCᴰ ℓCᴰ'
  CartesianCategoryⱽ→SCwFⱽ .fst = Cⱽ.Cᴰ
  CartesianCategoryⱽ→SCwFⱽ .snd .fst = Cⱽ.Cᴰ.ob[_]
  CartesianCategoryⱽ→SCwFⱽ .snd .snd .fst = Cⱽ.Cᴰ [-][-,_]
  CartesianCategoryⱽ→SCwFⱽ .snd .snd .snd .fst = Cⱽ.termⱽ
  CartesianCategoryⱽ→SCwFⱽ .snd .snd .snd .snd .fst = Cⱽ.cartesianLifts
  CartesianCategoryⱽ→SCwFⱽ .snd .snd .snd .snd .snd .fst = Cⱽ.bpⱽ
  CartesianCategoryⱽ→SCwFⱽ .snd .snd .snd .snd .snd .snd =
    isCatFibration→YoFibrations Cⱽ.cartesianLifts
