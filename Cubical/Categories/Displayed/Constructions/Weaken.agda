{-

  Weaken a category to be a displayed category.

  Later: weaken a displayed category to depend on fewer parameters?

-}

{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Constructions.Weaken where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Terminal hiding (intro)

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category
  weaken : Categoryᴰ C ℓD ℓD'
  weaken .ob[_] x = D .ob
  weaken .Hom[_][_,_] f d d' = D [ d , d' ]
  weaken .idᴰ = D .id
  weaken ._⋆ᴰ_ = D ._⋆_
  weaken .⋆IdLᴰ = D .⋆IdL
  weaken .⋆IdRᴰ = D .⋆IdR
  weaken .⋆Assocᴰ = D .⋆Assoc
  weaken .isSetHomᴰ = D .isSetHom

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {E : Category ℓE ℓE'}
         {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
         (FC : Functor E C)
         (FD : Functor E D)
         where
  open Category
  open Functor
  open Functorᴰ
  intro : Functorᴰ FC Eᴰ (weaken C D)
  intro .F-obᴰ {x} _ = FD .F-ob x
  intro .F-homᴰ {f = f} _ = FD .F-hom f
  intro .F-idᴰ = FD .F-id
  intro .F-seqᴰ _ _ = FD .F-seq _ _
module _ {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} where
  open Functor
  open Functorᴰ

  weakenF : {D : Category ℓD ℓD'} {E : Category ℓE ℓE'} {F : Functor B C}
          → (G : Functor D E)
          → Functorᴰ F (weaken B D) (weaken C E)
  weakenF G .F-obᴰ = G .F-ob
  weakenF G .F-homᴰ = G .F-hom
  weakenF G .F-idᴰ = G .F-id
  weakenF G .F-seqᴰ = G .F-seq
