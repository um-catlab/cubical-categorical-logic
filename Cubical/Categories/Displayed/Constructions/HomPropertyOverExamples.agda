module Cubical.Categories.Displayed.Constructions.HomPropertyOverExamples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.HomPropertyOver

private
  variable
    ℓC ℓC' : Level

module _ (C : Category ℓC ℓC') where
  open Category hiding (_∘_)

  private
    module C = Category C

    isIsoC = isIso C

    idIsIsoC : ∀ {x} → isIsoC (C.id {x})
    idIsIsoC = idCatIso .snd

    compP : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]} → isIsoC f → isIsoC g → isIsoC (f C.⋆ g)
    compP {f = f} {g = g} fIso gIso = ⋆Iso (f , fIso) (g , gIso) .snd

  -- Given as an example of a wide subcategory on nlab:
  -- https://ncatlab.org/nlab/show/core+groupoid
  Coreᴰ : Categoryᴰ C ℓ-zero ℓC'
  Coreᴰ = HomPropertyOver C isIsoC (isPropIsIso _) idIsIsoC compP

  Core : Category ℓC ℓC'
  Core = ∫C Coreᴰ

  private
    module Core = Category Core

  isIsoC→isIsoCore : ∀ {x y} (f : C [ x , y ]) (iso : isIso C f) → isIso Core (f , iso)
  isIsoC→isIsoCore f iso .isIso.inv = invIso (f , iso)
  isIsoC→isIsoCore f iso .isIso.sec = Σ≡Prop isPropIsIso (iso .isIso.sec)
  isIsoC→isIsoCore f iso .isIso.ret = Σ≡Prop isPropIsIso (iso .isIso.ret)

  morCore→isIsoC : ∀ {x y} (f : Core [ x , y ]) → isIso C (f .fst)
  morCore→isIsoC f =  f .snd

  morCore→isIsoCore : ∀ {x y} (f : Core [ x , y ]) → isIso Core f
  morCore→isIsoCore (f , iso) = isIsoC→isIsoCore f iso
