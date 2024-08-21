{-
  The free fibration of categories with families?
-}

{-# OPTIONS --safe #-}
module Syntax.FreeCwFFib where

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
module FreeSCwFFib
  (C : Category ℓC ℓC')
  (Ty : Type ℓT)
  (TM : ∀ (A : Ty) → Presheaf C ℓT')
  (GTy : Ty → Type ℓTᴰ)
  where
  Tm : C .ob → Ty → Type ℓT'
  Tm Γ A = ⟨ TM A ⟅ Γ ⟆ ⟩

  data Ctxᴰ (Γ : C .ob) : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓT ℓT')) ℓTᴰ)
  data Tyᴰ (A : Ty) : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓT ℓT')) ℓTᴰ)
  data Ctxᴰ Γ where
    ⊤ₑ : Ctxᴰ Γ
    _∧ₑ_ : Ctxᴰ Γ → Ctxᴰ Γ → Ctxᴰ Γ
    pb-subst : ∀ {Δ} (δ : C [ Γ , Δ ]) → Ctxᴰ Δ → Ctxᴰ Γ
    pb-tm    : ∀ {A} (M : Tm Γ A) → Tyᴰ A → Ctxᴰ Γ
  data Tyᴰ A where
    iTy : GTy A → Tyᴰ A

  
