{-

  Simple categories with families are one approach to modeling the
  judgmental structure of simply typed lambda calculus.

  Definition 9 in https://arxiv.org/abs/1904.00827

-}
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
open import Cubical.Categories.Displayed.Limits.CartesianD
open import Cubical.Categories.Displayed.Limits.CartesianV
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
  CartesianCategory→SCwF .SCwF.C = CC.C
  CartesianCategory→SCwF .SCwF.Ty = CC.C .ob
  CartesianCategory→SCwF .SCwF.Tm = CC.C [-,_]
  CartesianCategory→SCwF .SCwF.term = CC.term
  CartesianCategory→SCwF .SCwF.comprehension x y = CC.bp (y , x)

module _
  {C : CartesianCategory ℓC ℓC'}
  (Cᴰ : CartesianCategoryᴰ C ℓCᴰ ℓCᴰ')
  where
  private
    module Cᴰ = CartesianCategoryᴰ Cᴰ
  CartesianCategoryᴰ→SCwFᴰ : SCwFᴰ (CartesianCategory→SCwF C) ℓCᴰ ℓCᴰ' ℓCᴰ ℓCᴰ'
  CartesianCategoryᴰ→SCwFᴰ .SCwFᴰ.Cᴰ = Cᴰ.Cᴰ
  CartesianCategoryᴰ→SCwFᴰ .SCwFᴰ.Tyᴰ = Cᴰ.Cᴰ.ob[_]
  CartesianCategoryᴰ→SCwFᴰ .SCwFᴰ.Tmᴰ = Cᴰ.Cᴰ [-][-,_]
  CartesianCategoryᴰ→SCwFᴰ .SCwFᴰ.termᴰ = Cᴰ.termᴰ
  CartesianCategoryᴰ→SCwFᴰ .SCwFᴰ.comprehensionᴰ Γᴰ Aᴰ = Cᴰ.bpᴰ (Aᴰ , Γᴰ)

module _
  {C : CartesianCategory ℓC ℓC'}
  (Cⱽ : CartesianCategoryⱽ (C .CartesianCategory.C) ℓCᴰ ℓCᴰ')
  where
  private
    module Cⱽ = CartesianCategoryⱽ Cⱽ
  CartesianCategoryⱽ→SCwFⱽ : SCwFⱽ (CartesianCategory→SCwF C) ℓCᴰ ℓCᴰ' ℓCᴰ ℓCᴰ'
  CartesianCategoryⱽ→SCwFⱽ .SCwFⱽ.Cᴰ = Cⱽ.Cᴰ
  CartesianCategoryⱽ→SCwFⱽ .SCwFⱽ.Tyᴰ = Cⱽ.Cᴰ.ob[_]
  CartesianCategoryⱽ→SCwFⱽ .SCwFⱽ.Tmᴰ = Cⱽ.Cᴰ [-][-,_]
  CartesianCategoryⱽ→SCwFⱽ .SCwFⱽ.terminalsⱽ = Cⱽ.termⱽ
  CartesianCategoryⱽ→SCwFⱽ .SCwFⱽ.isFib = Cⱽ.cartesianLifts
  CartesianCategoryⱽ→SCwFⱽ .SCwFⱽ.binProductsⱽ = Cⱽ.bpⱽ
  CartesianCategoryⱽ→SCwFⱽ .SCwFⱽ.TmᴰFib = Cⱽ.cartesianLifts
