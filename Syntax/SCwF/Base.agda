{-
  The free fibration of simple categories with families?
-}

{-# OPTIONS --safe #-}
module Syntax.SCwF.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Displayed.Limits.BinProduct.Concrete
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Agda.Builtin.Cubical.Equiv
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Foundations.Univalence

private
  variable
    ℓC ℓC' ℓT ℓT' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' ℓCᴰᴰ ℓCᴰᴰ' : Level

open Category
open Functor
SCwF : (ℓC ℓC' ℓT ℓT' : Level) → Type _
SCwF ℓC ℓC' ℓT ℓT' =
  Σ[ C ∈  Category ℓC ℓC' ]
  Σ[ Ty ∈ Type ℓT ]
  (∀ (A : Ty) → Presheaf C ℓT')

module SCwF (CT : SCwF ℓC ℓC' ℓT ℓT') where
  C = CT .fst
  Ty = CT .snd .fst
  TM = CT .snd .snd

SCwFᴰ : (CT : SCwF ℓC ℓC' ℓT ℓT') (ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level) → Type _
SCwFᴰ CT ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' =
  let open SCwF CT in
  Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
  Σ[ Tyᴰ ∈ (Ty → Type ℓTᴰ) ]
  (∀ {A : Ty}(Aᴰ : Tyᴰ A) → Presheafᴰ Cᴰ (TM A) ℓTᴰ')

module SCwFᴰ {CT : SCwF ℓC ℓC' ℓT ℓT'} (CTᴰ : SCwFᴰ CT ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') where
  Cᴰ = CTᴰ .fst
  Tyᴰ = CTᴰ .snd .fst
  TMᴰ = CTᴰ .snd .snd

  -- isCartesianLift : 

isFibᴰ : {CT : SCwF ℓC ℓC' ℓT ℓT'} (CTᴰ : SCwFᴰ CT ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') → Type _
isFibᴰ CTᴰ =
  isFibration Cᴰ
  × VerticalTerminals Cᴰ
  × VerticalBinProducts Cᴰ
  × {!!}
  where
  open SCwFᴰ CTᴰ
