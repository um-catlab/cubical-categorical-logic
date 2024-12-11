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

open import Cubical.Categories.WithFamilies.Simple.Base

open Category
open UniversalElement
CartesianCategory→SCwF : {ℓC ℓC' : Level}
  → CartesianCategory ℓC ℓC'
  → SCwF ℓC ℓC' ℓC ℓC'
CartesianCategory→SCwF CC .fst = CC .fst
CartesianCategory→SCwF CC .snd .fst = CC .fst .ob
CartesianCategory→SCwF CC .snd .snd .fst x = CC .fst [-, x ]
CartesianCategory→SCwF CC .snd .snd .snd .fst = CC .snd .fst
CartesianCategory→SCwF CC .snd .snd .snd .snd x y =
  BinProductToRepresentable (CC .fst) (CC .snd .snd x y)
