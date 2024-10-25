-- Product of two categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.BinProduct.More where

open import Cubical.Categories.Constructions.BinProduct

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Instances.Functors.More

open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open Category
open Functor

module _ (C : Category ℓC ℓC')
         (D : Category ℓD ℓD') where
  open Functor

  module _ (E : Category ℓE ℓE') where
    ×C-assoc⁻ : Functor ((C ×C D) ×C E) (C ×C (D ×C E))
    ×C-assoc⁻ .F-ob = λ z → z .fst .fst , z .fst .snd , z .snd
    ×C-assoc⁻ .F-hom x = x .fst .fst , x .fst .snd , x .snd
    ×C-assoc⁻ .F-id = refl
    ×C-assoc⁻ .F-seq f g = refl

module _ (C : Category ℓC ℓC')
         (D : Category ℓD ℓD') where
  open Functor
  SplitCatIso× : {x y : C .ob}{z w : D .ob}
    → CatIso (C ×C D) (x , z) (y , w)
    → CatIso C x y × CatIso D z w
  SplitCatIso× f .fst .fst = f .fst .fst
  SplitCatIso× f .fst .snd .isIso.inv = f .snd .isIso.inv .fst
  SplitCatIso× f .fst .snd .isIso.sec = cong fst (f .snd .isIso.sec)
  SplitCatIso× f .fst .snd .isIso.ret = cong fst (f .snd .isIso.ret)
  SplitCatIso× f .snd .fst = f .fst .snd
  SplitCatIso× f .snd .snd .isIso.inv = f .snd .isIso.inv .snd
  SplitCatIso× f .snd .snd .isIso.sec = cong snd (f .snd .isIso.sec)
  SplitCatIso× f .snd .snd .isIso.ret = cong snd (f .snd .isIso.ret)

private
  variable
    A A' : Category ℓA ℓA'
    B B' : Category ℓB ℓB'
    C C' : Category ℓC ℓC'
    D D' : Category ℓD ℓD'
    F F' : Functor A B
    G G' : Functor C D

module _ {A : Category ℓA ℓA'}
    {B : Category ℓB ℓB'}
    {C : Category ℓC ℓC'}
    {D : Category ℓD ℓD'}
    {F F' : Functor A B}
    {G G' : Functor C D}
  where
  open NatTrans
  NatTrans× :
    NatTrans F F' → NatTrans G G' →
    NatTrans (F ×F G) (F' ×F G')
  NatTrans× α β .N-ob x .fst = α ⟦ x .fst ⟧
  NatTrans× α β .N-ob x .snd = β ⟦ x .snd ⟧
  NatTrans× α β .N-hom (f , g) = ΣPathP ((α .N-hom f) , (β .N-hom g))

  open NatIso
  open isIso
  NatIso× :
    NatIso F F' → NatIso G G' → NatIso (F ×F G) (F' ×F G')
  NatIso× α β .trans = NatTrans× (α .trans) (β .trans)
  NatIso× α β .nIso (x , y) = CatIso× _ _ (NatIsoAt α x) (NatIsoAt β y) .snd
