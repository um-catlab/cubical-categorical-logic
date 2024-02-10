{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Base.More where


open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

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

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  open Functor

  Fst :  Functor (∫C Cᴰ) C
  Fst .F-ob = fst
  Fst .F-hom = fst
  Fst .F-id = refl
  Fst .F-seq =
    λ f g → cong {x = f ⋆⟨ ∫C Cᴰ ⟩ g} fst refl

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  private
    module Cᴰ = Categoryᴰ Cᴰ

  open Categoryᴰ
  _^opᴰ : Categoryᴰ (C ^op) ℓCᴰ ℓCᴰ'
  _^opᴰ .ob[_] x = Cᴰ.ob[ x ]
  _^opᴰ .Hom[_][_,_] f xᴰ yᴰ = Cᴰ.Hom[ f ][ yᴰ , xᴰ ]
  _^opᴰ .idᴰ = Cᴰ.idᴰ
  _^opᴰ ._⋆ᴰ_ fᴰ gᴰ = gᴰ Cᴰ.⋆ᴰ fᴰ
  _^opᴰ .⋆IdLᴰ = Cᴰ .⋆IdRᴰ
  _^opᴰ .⋆IdRᴰ = Cᴰ .⋆IdLᴰ
  _^opᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = symP (Cᴰ.⋆Assocᴰ _ _ _)
  _^opᴰ .isSetHomᴰ = Cᴰ .isSetHomᴰ

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where
  open Functorᴰ
  _^opFᴰ : Functorᴰ (F ^opF) (Cᴰ ^opᴰ) (Dᴰ ^opᴰ)
  _^opFᴰ .F-obᴰ = Fᴰ .F-obᴰ
  _^opFᴰ .F-homᴰ = Fᴰ .F-homᴰ
  _^opFᴰ .F-idᴰ = Fᴰ .F-idᴰ
  _^opFᴰ .F-seqᴰ fᴰ gᴰ = Fᴰ .F-seqᴰ gᴰ fᴰ

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  private
    module C = Category C
    module D = Category D

  open Categoryᴰ Dᴰ
  open Functor F
  open Functorᴰ

  forgetReindex : Functorᴰ F (reindex Dᴰ F) Dᴰ
  forgetReindex .F-obᴰ = λ z → z
  forgetReindex .F-homᴰ = λ z → z
  forgetReindex .F-idᴰ = symP (transport-filler _ _)
  forgetReindex .F-seqᴰ fᴰ gᴰ = symP (transport-filler _ _)
