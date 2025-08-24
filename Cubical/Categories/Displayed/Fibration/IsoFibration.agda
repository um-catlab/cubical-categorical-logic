module Cubical.Categories.Displayed.Fibration.IsoFibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓP' : Level

open Category
open Functorᴰ
open isIso

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  record WeakIsoLift {c c'}
    (cᴰ : Cᴰ.ob[ c' ]) (f : CatIso C c c')
    : Type (ℓ-max ℓCᴰ ℓCᴰ')
    where
    field
      f*cᴰ : Cᴰ.ob[ c ]
      π : Cᴰ.Hom[ f .fst ][ f*cᴰ , cᴰ ]
      σ : Cᴰ.Hom[ f .snd .inv ][ cᴰ , f*cᴰ ]

  record WeakIsoLift' {c c'}
    (cᴰ : Cᴰ.ob[ c ]) (f : CatIso C c c')
    : Type (ℓ-max ℓCᴰ ℓCᴰ')
    where
    field
      f*cᴰ : Cᴰ.ob[ c' ]
      σ : Cᴰ.Hom[ f .fst ][ cᴰ , f*cᴰ ]
      π : Cᴰ.Hom[ f .snd .inv ][ f*cᴰ , cᴰ ]

  isWeakIsoFibration : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
  isWeakIsoFibration = ∀ {c c'} (cᴰ : Cᴰ.ob[ c' ]) (f : CatIso C c c')
    → WeakIsoLift cᴰ f

  isWeakIsoFibration' : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
  isWeakIsoFibration' = ∀ {c c'} (cᴰ : Cᴰ.ob[ c ]) (f : CatIso C c c')
    → WeakIsoLift' cᴰ f
