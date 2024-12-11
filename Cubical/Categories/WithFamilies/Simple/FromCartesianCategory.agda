{-

  Most SCwFs arise from cartesian categories

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.WithFamilies.Simple.FromCartesianCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
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

CartesianCategory→SCwF : {ℓC ℓC' : Level}
  → CartesianCategory ℓC ℓC'
  → SCwF ℓC ℓC' ℓC ℓC'
CartesianCategory→SCwF CC .fst = CC .fst
CartesianCategory→SCwF CC .snd .fst = CC .fst .ob
CartesianCategory→SCwF CC .snd .snd .fst x = CC .fst [-, x ]
CartesianCategory→SCwF CC .snd .snd .snd .fst = CC .snd .fst
CartesianCategory→SCwF CC .snd .snd .snd .snd x y =
  BinProductToRepresentable (CC .fst) (CC .snd .snd x y)

module _
  {C : CartesianCategory ℓC ℓC'}
  (Cᴰ : CartesianCategoryᴰ C ℓCᴰ ℓCᴰ')
  where
  CartesianCategoryᴰ→SCwFᴰ : SCwFᴰ (CartesianCategory→SCwF C) ℓCᴰ ℓCᴰ' ℓCᴰ ℓCᴰ'
  CartesianCategoryᴰ→SCwFᴰ .fst = Cᴰ .fst
  CartesianCategoryᴰ→SCwFᴰ .snd .fst = Cᴰ .fst .ob[_]
  CartesianCategoryᴰ→SCwFᴰ .snd .snd .fst xᴰ = Cᴰ .fst [-][-, xᴰ ]
  CartesianCategoryᴰ→SCwFᴰ .snd .snd .snd .fst = Cᴰ .snd .fst
  CartesianCategoryᴰ→SCwFᴰ .snd .snd .snd .snd Γᴰ Aᴰ =
    BinProductᴰ→BinProductᴰPsh (Cᴰ .fst) (Cᴰ .snd .snd (Γᴰ , Aᴰ))

module _
  {C : CartesianCategory ℓC ℓC'}
  (Cⱽ : CartesianCategoryⱽ (C .fst) ℓCᴰ ℓCᴰ')
  where
  opaque
    CartesianCategoryⱽ→SCwFⱽ : SCwFⱽ (CartesianCategory→SCwF C) ℓCᴰ ℓCᴰ' ℓCᴰ ℓCᴰ'
    CartesianCategoryⱽ→SCwFⱽ .fst = Cⱽ .fst
    CartesianCategoryⱽ→SCwFⱽ .snd .fst = Cⱽ .fst .ob[_]
    CartesianCategoryⱽ→SCwFⱽ .snd .snd .fst xᴰ = Cⱽ .fst [-][-, xᴰ ]
    CartesianCategoryⱽ→SCwFⱽ .snd .snd .snd .fst = Cⱽ .snd .snd .fst
    CartesianCategoryⱽ→SCwFⱽ .snd .snd .snd .snd .fst = Cⱽ .snd .fst
    CartesianCategoryⱽ→SCwFⱽ .snd .snd .snd .snd .snd .fst = Cⱽ .snd .snd .snd
    CartesianCategoryⱽ→SCwFⱽ .snd .snd .snd .snd .snd .snd M Aᴰ =
      fibLift→PshᴰLift (Cⱽ .snd .fst Aᴰ M)
