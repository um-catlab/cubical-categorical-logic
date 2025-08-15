{-

  A displayed SCwF is an abstract notion of "logical family" over a SCwF

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.WithFamilies.Simple.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory
-- open import Cubical.Categories.Constructions.TotalCategory.Limits
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.WithFamilies.Simple.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Section
import Cubical.Categories.Displayed.Presheaf.CartesianLift as Presheafᴰ

private
  variable
    ℓC ℓC' ℓT ℓT' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level

open UniversalElement
open UniversalElementᴰ
open Bifunctorᴰ
open isIsoOver
open Iso

SCwFᴰ : (C : SCwF ℓC ℓC' ℓT ℓT') → (ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level) → Type _
SCwFᴰ (C , Ty , Tm , term , comprehension) ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' =
  Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
  let module Cᴰ = Categoryᴰ Cᴰ in
  Σ[ Tyᴰ ∈ (Ty → Type ℓTᴰ) ]
  Σ[ Tmᴰ ∈ (∀ {A} (Aᴰ : Tyᴰ A) → Presheafᴰ (Tm A) Cᴰ ℓTᴰ') ]
  Terminalᴰ Cᴰ term ×
  (∀ {Γ A} (Γᴰ : Cᴰ.ob[ Γ ])(Aᴰ : Tyᴰ A) →
    UniversalElementᴰ Cᴰ
      (comprehension Γ A)
      (PshProdᴰ .Bif-obᴰ (Cᴰ [-][-, Γᴰ ]) (Tmᴰ Aᴰ)))

SCwFⱽ : (C : SCwF ℓC ℓC' ℓT ℓT') → (ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level) → Type _
SCwFⱽ (C , Ty , Tm , term , comprehension) ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' =
  Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
  let module Cᴰ = Categoryᴰ Cᴰ in
  Σ[ Tyᴰ ∈ (Ty → Type ℓTᴰ) ]
  Σ[ Tmᴰ ∈ (∀ {A} (Aᴰ : Tyᴰ A) → Presheafᴰ (Tm A) Cᴰ ℓTᴰ') ]
  Terminalsⱽ Cᴰ ×
  isFibration Cᴰ ×
  BinProductsⱽ Cᴰ ×
  (∀ {A} (Aᴰ : Tyᴰ A) → Presheafᴰ.isFibration (Tmᴰ Aᴰ))
