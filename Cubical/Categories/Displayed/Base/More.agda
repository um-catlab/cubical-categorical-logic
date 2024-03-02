{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Base.More where

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
open import Cubical.Categories.Displayed.Instances.Terminal

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

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
  open Functorᴰ

  Fst : Functor (∫C Cᴰ) C
  Fst .F-ob = fst
  Fst .F-hom = fst
  Fst .F-id = refl
  Fst .F-seq =
    λ f g → cong {x = f ⋆⟨ ∫C Cᴰ ⟩ g} fst refl

  -- TODO : There was a comment here with a Snd stub
  -- I think this is what you wanted to do?
  Snd : Functorᴰ Fst (weaken (∫C Cᴰ) C) Cᴰ
  Snd .F-obᴰ {x} _ = x .snd
  Snd .F-homᴰ {_}{_}{f} _ = f .snd
  Snd .F-idᴰ = refl
  Snd .F-seqᴰ _ _ = refl

  module _ {D : Category ℓD ℓD'}
           (F : Functor D C)
           (Fᴰ : Functorᴰ F (Unitᴰ D) Cᴰ)
           where
    mk∫Functor : Functor D (∫C Cᴰ)
    mk∫Functor .F-ob d = F ⟅ d ⟆ , Fᴰ .F-obᴰ _
    mk∫Functor .F-hom f = (F ⟪ f ⟫) , (Fᴰ .F-homᴰ _)
    mk∫Functor .F-id = ΣPathP (F .F-id , Fᴰ .F-idᴰ)
    mk∫Functor .F-seq f g = ΣPathP (F .F-seq f g , Fᴰ .F-seqᴰ _ _)

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
  where

  open Functorᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  Fstᴰ : Functorᴰ Id (∫Cᴰ Cᴰ Dᴰ) Cᴰ
  Fstᴰ .F-obᴰ = fst
  Fstᴰ .F-homᴰ = fst
  Fstᴰ .F-idᴰ = refl
  Fstᴰ .F-seqᴰ _ _ = refl

  module _ {E : Category ℓE ℓE'} (F : Functor E C)
           {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
           (Fᴰ : Functorᴰ F Eᴰ Cᴰ)
           (Gᴰ : Functorᴰ (∫F Fᴰ) (Unitᴰ (∫C Eᴰ)) Dᴰ)
           where

    mk∫ᴰFunctorᴰ : Functorᴰ F Eᴰ (∫Cᴰ Cᴰ Dᴰ)
    mk∫ᴰFunctorᴰ .F-obᴰ xᴰ = Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ _
    mk∫ᴰFunctorᴰ .F-homᴰ fᴰ = (Fᴰ .F-homᴰ fᴰ) , (Gᴰ .F-homᴰ _)
    mk∫ᴰFunctorᴰ .F-idᴰ = ΣPathP (Fᴰ .F-idᴰ , Gᴰ .F-idᴰ)
    mk∫ᴰFunctorᴰ .F-seqᴰ fᴰ gᴰ = ΣPathP (Fᴰ .F-seqᴰ fᴰ gᴰ , Gᴰ .F-seqᴰ _ _)

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

