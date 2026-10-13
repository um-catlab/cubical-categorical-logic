{-
    Binary Product of displayed categories over the same base.

    TODO: this can be defined as an instance of TotalCategoryᴰ using
    weakening. Should it?

-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.BinProduct.More where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Instances.TotalCategory
  as TotalCat hiding (Fst; Snd)
open import Cubical.Categories.Displayed.Instances.TotalCategory
  as TotalCatᴰ hiding (introS; introF; Fstᴰ)
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
  hiding (introF)
open import Cubical.Categories.Displayed.Instances.Functor
open import Cubical.Categories.Displayed.Reasoning as Reasoning
private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level
    ℓBᴰ ℓBᴰ' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level
    ℓDᴰ₀ ℓDᴰ₀' ℓDᴰ₁ ℓDᴰ₁' ℓE ℓE' ℓEᴰ ℓEᴰ' ℓEᴰ₀ ℓEᴰ₀' ℓEᴰ₁ ℓEᴰ₁' : Level

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
  where

  open Functorᴰ
  private
    module D = Categoryᴰ D

  ΔCᴰ : Functorᴰ (Δ C) D (D ×Cᴰ D)
  ΔCᴰ .F-obᴰ xᴰ = xᴰ , xᴰ
  ΔCᴰ .F-homᴰ fᴰ = fᴰ , fᴰ
  ΔCᴰ .F-idᴰ = refl
  ΔCᴰ .F-seqᴰ fᴰ gᴰ = refl

  Δᴰ : Functorᴰ Id D (D ×ᴰ D)
  Δᴰ .F-obᴰ xᴰ = xᴰ , xᴰ
  Δᴰ .F-homᴰ fᴰ = fᴰ , fᴰ
  Δᴰ .F-idᴰ = refl
  Δᴰ .F-seqᴰ fᴰ gᴰ = refl

module _
  {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {D : Category ℓD ℓD'} (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  where
  Fstᴰ : Functorᴰ (Fst C D) (Cᴰ ×Cᴰ Dᴰ) Cᴰ
  Fstᴰ .Functorᴰ.F-obᴰ = fst
  Fstᴰ .Functorᴰ.F-homᴰ = fst
  Fstᴰ .Functorᴰ.F-idᴰ = refl
  Fstᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ = refl

  Sndᴰ : Functorᴰ (Snd C D) (Cᴰ ×Cᴰ Dᴰ) Dᴰ
  Sndᴰ .Functorᴰ.F-obᴰ = snd
  Sndᴰ .Functorᴰ.F-homᴰ = snd
  Sndᴰ .Functorᴰ.F-idᴰ = refl
  Sndᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ = refl
  module _ {E : Category ℓE ℓE'} (Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ') where
    ×Cᴰ-assoc : Functorᴰ (×C-assoc C D E)
      (Cᴰ ×Cᴰ (Dᴰ ×Cᴰ Eᴰ))
      ((Cᴰ ×Cᴰ Dᴰ) ×Cᴰ Eᴰ)
    ×Cᴰ-assoc .Functorᴰ.F-obᴰ x = (x .fst , x .snd .fst) , x .snd .snd
    ×Cᴰ-assoc .Functorᴰ.F-homᴰ x = (x .fst , x .snd .fst) , x .snd .snd
    ×Cᴰ-assoc .Functorᴰ.F-idᴰ = refl
    ×Cᴰ-assoc .Functorᴰ.F-seqᴰ _ _ = refl

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
  rinjᴰ : ∀ {c} → Cᴰ.ob[ c ] → Functorᴰ (rinj C D c) Dᴰ (Cᴰ ×Cᴰ Dᴰ)
  rinjᴰ cᴰ .Functorᴰ.F-obᴰ = λ z → cᴰ , z
  rinjᴰ cᴰ .Functorᴰ.F-homᴰ = λ z → Cᴰ.idᴰ , z
  rinjᴰ cᴰ .Functorᴰ.F-idᴰ = refl
  rinjᴰ cᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ = ΣPathP ((symP (Cᴰ.⋆IdRᴰ _)) , refl)

  linjᴰ : ∀ {d} → Dᴰ.ob[ d ] → Functorᴰ (linj C D d) Cᴰ (Cᴰ ×Cᴰ Dᴰ)
  linjᴰ dᴰ .Functorᴰ.F-obᴰ = λ z → z , dᴰ
  linjᴰ dᴰ .Functorᴰ.F-homᴰ x = x , Dᴰ.idᴰ
  linjᴰ dᴰ .Functorᴰ.F-idᴰ = refl
  linjᴰ dᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ = ΣPathP (refl , (symP (Dᴰ.⋆IdRᴰ _)))

module _
  {B : Category ℓB ℓB'} {Bᴰ : Categoryᴰ B ℓBᴰ ℓBᴰ'}
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {E : Category ℓE ℓE'} {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
  {F : Functor B C}{G : Functor D E}
  (Fᴰ : Functorᴰ F Bᴰ Cᴰ) (Gᴰ : Functorᴰ G Dᴰ Eᴰ)
  where
  open Functorᴰ
  private
    module RCᴰ = Reasoning Cᴰ
    module REᴰ = Reasoning Eᴰ
  _×Fᴰ_ : Functorᴰ (F ×F G) (Bᴰ ×Cᴰ Dᴰ) (Cᴰ ×Cᴰ Eᴰ)
  _×Fᴰ_ .F-obᴰ x = (F-obᴰ Fᴰ (x .fst)) , (F-obᴰ Gᴰ (x .snd))
  _×Fᴰ_ .F-homᴰ f = F-homᴰ Fᴰ (f .fst) , F-homᴰ Gᴰ (f .snd)
  _×Fᴰ_ .F-idᴰ = ΣPathP (RCᴰ.rectify (F-idᴰ Fᴰ) , REᴰ.rectify (Gᴰ .F-idᴰ))
  _×Fᴰ_ .F-seqᴰ fᴰ gᴰ =
    ΣPathP ((RCᴰ.rectify (Fᴰ .F-seqᴰ _ _)) , REᴰ.rectify (Gᴰ .F-seqᴰ _ _))

module _ {C : Category ℓC ℓC'}
  {Dᴰ₀ : Categoryᴰ C ℓDᴰ₀ ℓDᴰ₀'} {Dᴰ₁ : Categoryᴰ C ℓDᴰ₁ ℓDᴰ₁'}
  {E : Category ℓE ℓE'}
  (F : Functor E C)
  (Fᴰ₀ : Section F Dᴰ₀)
  (Fᴰ₁ : Section F Dᴰ₁)
  where

  open Section
  introS : Section F (Dᴰ₀ ×ᴰ Dᴰ₁)
  introS .F-obᴰ d =  Fᴰ₀ .F-obᴰ d , Fᴰ₁ .F-obᴰ d
  introS .F-homᴰ fᴰ = Fᴰ₀ .F-homᴰ fᴰ , Fᴰ₁ .F-homᴰ fᴰ
  introS .F-idᴰ = ΣPathP (Fᴰ₀ .F-idᴰ , Fᴰ₁ .F-idᴰ)
  introS .F-seqᴰ fᴰ gᴰ = ΣPathP (Fᴰ₀ .F-seqᴰ fᴰ gᴰ , Fᴰ₁ .F-seqᴰ fᴰ gᴰ)

module _ {C : Category ℓC ℓC'}
  {Dᴰ₀ : Categoryᴰ C ℓDᴰ₀ ℓDᴰ₀'} {Dᴰ₁ : Categoryᴰ C ℓDᴰ₁ ℓDᴰ₁'}
  {E : Category ℓE ℓE'} {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
  (F : Functor E C)
  (Fᴰ₀ : Functorᴰ F Eᴰ Dᴰ₀)
  (Fᴰ₁ : Functorᴰ F Eᴰ Dᴰ₁)
  where

  introF : Functorᴰ F Eᴰ (Dᴰ₀ ×ᴰ Dᴰ₁)
  introF = TotalCat.recᴰ F _
    (introS _ (TotalCat.elim Fᴰ₀) (TotalCat.elim Fᴰ₁))

private
  -- In principle we can also define introS in terms of introF in
  -- terms of Functorᴰs as follows:
  module _ {C : Category ℓC ℓC'}
    {Dᴰ₀ : Categoryᴰ C ℓDᴰ₀ ℓDᴰ₀'} {Dᴰ₁ : Categoryᴰ C ℓDᴰ₁ ℓDᴰ₁'}
    {E : Category ℓE ℓE'}
    (F : Functor E C)
    (Fᴰ₀ : Section F Dᴰ₀)
    (Fᴰ₁ : Section F Dᴰ₁)
    where

    open Section
    introS' : Section F (Dᴰ₀ ×ᴰ Dᴰ₁)
    introS' = compFunctorᴰGlobalSection
      (introF F (Unitᴰ.recᴰ Fᴰ₀) (Unitᴰ.recᴰ Fᴰ₁))
      ttS

module _ {C : Category ℓC ℓC'}
  (Dᴰ₀ : Categoryᴰ C ℓDᴰ₀ ℓDᴰ₀') (Dᴰ₁ : Categoryᴰ C ℓDᴰ₁ ℓDᴰ₁') where
  Fstⱽ : Functorⱽ (Dᴰ₀ ×ᴰ Dᴰ₁) Dᴰ₀
  Fstⱽ .Functorᴰ.F-obᴰ = fst
  Fstⱽ .Functorᴰ.F-homᴰ = fst
  Fstⱽ .Functorᴰ.F-idᴰ = refl
  Fstⱽ .Functorᴰ.F-seqᴰ fᴰ gᴰ = refl

  Sndⱽ : Functorⱽ (Dᴰ₀ ×ᴰ Dᴰ₁) Dᴰ₁
  Sndⱽ .Functorᴰ.F-obᴰ = snd
  Sndⱽ .Functorᴰ.F-homᴰ = snd
  Sndⱽ .Functorᴰ.F-idᴰ = refl
  Sndⱽ .Functorᴰ.F-seqᴰ fᴰ gᴰ = refl

module _ {C : Category ℓC ℓC'}
  {Dᴰ₀ : Categoryᴰ C ℓDᴰ₀ ℓDᴰ₀'} {Dᴰ₁ : Categoryᴰ C ℓDᴰ₁ ℓDᴰ₁'}
  {E : Category ℓE ℓE'} {Eᴰ₀ : Categoryᴰ E ℓEᴰ₀ ℓEᴰ₀'}{Eᴰ₁ : Categoryᴰ E ℓEᴰ₁ ℓEᴰ₁'}
  {F : Functor E C}
  where
  _×ᴰF_ : (Fᴰ₀ : Functorᴰ F Eᴰ₀ Dᴰ₀) (Fᴰ₁ : Functorᴰ F Eᴰ₁ Dᴰ₁)
    → Functorᴰ F (Eᴰ₀ ×ᴰ Eᴰ₁) (Dᴰ₀ ×ᴰ Dᴰ₁)
  Fᴰ₀ ×ᴰF Fᴰ₁ = introF F (Fᴰ₀ ∘Fᴰⱽ Fstⱽ Eᴰ₀ Eᴰ₁) (Fᴰ₁ ∘Fᴰⱽ Sndⱽ Eᴰ₀ Eᴰ₁)

private
  variable
    ℓ ℓ' ℓC'' ℓC''' : Level
    C C' D D'  : Category ℓ ℓ'
    Cᴰ Cᴰ' Dᴰ'  : Categoryᴰ C ℓ ℓ'
open Functorᴰ

module _ {F : Functor C C'} {G : Functor C D'} where
  _,Fᴰ_ : (Fᴰ : Functorᴰ F Cᴰ Cᴰ') → (Gᴰ : Functorᴰ G Cᴰ Dᴰ')
    → Functorᴰ (F ,F G) Cᴰ (Cᴰ' ×Cᴰ Dᴰ')
  (Fᴰ ,Fᴰ Gᴰ) .F-obᴰ x = F-obᴰ Fᴰ x , F-obᴰ Gᴰ x
  (Fᴰ ,Fᴰ Gᴰ) .F-homᴰ x = F-homᴰ Fᴰ x , F-homᴰ Gᴰ x
  (Fᴰ ,Fᴰ Gᴰ) .F-idᴰ = ΣPathP ((Fᴰ .F-idᴰ) , (Gᴰ .F-idᴰ))
  (Fᴰ ,Fᴰ Gᴰ) .F-seqᴰ fᴰ gᴰ = ΣPathP ((Fᴰ .F-seqᴰ _ _) , Gᴰ .F-seqᴰ _ _)

open NatTrans
open NatTransᴰ
,Fᴰ-functorᴰ :
  Functorᴰ ,F-functor
    ((FUNCTORᴰ Cᴰ Cᴰ') ×Cᴰ (FUNCTORᴰ Cᴰ Dᴰ'))
    (FUNCTORᴰ Cᴰ (Cᴰ' ×Cᴰ Dᴰ'))
,Fᴰ-functorᴰ .F-obᴰ (Fᴰ , Gᴰ) = Fᴰ ,Fᴰ Gᴰ
,Fᴰ-functorᴰ .F-homᴰ (αᴰ , βᴰ) .N-obᴰ xᴰ = αᴰ .N-obᴰ xᴰ , βᴰ .N-obᴰ xᴰ
,Fᴰ-functorᴰ .F-homᴰ (αᴰ , βᴰ) .N-homᴰ fᴰ =
  ΣPathP (αᴰ .N-homᴰ fᴰ , βᴰ .N-homᴰ fᴰ)
,Fᴰ-functorᴰ .F-idᴰ = makeNatTransPathᴰ _ _ _ refl
,Fᴰ-functorᴰ .F-seqᴰ fᴰ gᴰ = makeNatTransPathᴰ _ _ _ refl

module _ {F : Functor C D} where
  _,Fⱽ_ : (Fᴰ : Functorᴰ F Cᴰ Cᴰ') (Fᴰ' : Functorᴰ F Cᴰ Dᴰ')
    → Functorᴰ F Cᴰ (Cᴰ' ×ᴰ Dᴰ')
  (Fᴰ ,Fⱽ Gᴰ) .F-obᴰ = λ z → F-obᴰ Fᴰ z , F-obᴰ Gᴰ z
  (Fᴰ ,Fⱽ Gᴰ) .F-homᴰ = λ z → F-homᴰ Fᴰ z , F-homᴰ Gᴰ z
  (Fᴰ ,Fⱽ Gᴰ) .F-idᴰ = ΣPathP (F-idᴰ Fᴰ , F-idᴰ Gᴰ)
  (Fᴰ ,Fⱽ Gᴰ) .F-seqᴰ fᴰ gᴰ = ΣPathP ((F-seqᴰ Fᴰ fᴰ gᴰ) , (F-seqᴰ Gᴰ fᴰ gᴰ))

,Fⱽ-functorⱽ :
  Functorⱽ
    ((FUNCTORᴰ Cᴰ Cᴰ') ×ᴰ (FUNCTORᴰ Cᴰ Dᴰ'))
    (FUNCTORᴰ Cᴰ (Cᴰ' ×ᴰ Dᴰ'))
,Fⱽ-functorⱽ .F-obᴰ {x = F} (Fᴰ , Fᴰ') = Fᴰ ,Fⱽ Fᴰ'
,Fⱽ-functorⱽ .F-homᴰ (αᴰ , βᴰ) .N-obᴰ xᴰ = (αᴰ .N-obᴰ xᴰ) , (βᴰ .N-obᴰ xᴰ)
,Fⱽ-functorⱽ .F-homᴰ (αᴰ , βᴰ) .N-homᴰ fᴰ =
  ΣPathP ((αᴰ .N-homᴰ fᴰ) , (βᴰ .N-homᴰ fᴰ))
,Fⱽ-functorⱽ .F-idᴰ = makeNatTransPathᴰ _ _ _ refl
,Fⱽ-functorⱽ .F-seqᴰ fᴰ gᴰ = makeNatTransPathᴰ _ _ _ refl
