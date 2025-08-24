{-

  Simple categories with families are one approach to modeling the
  judgmental structure of simply typed lambda calculus.

  Definition 9 in https://arxiv.org/abs/1904.00827

-}
module Cubical.Categories.WithFamilies.Simple.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions

open Category

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level
SCwF : (ℓC ℓC' ℓT ℓT' : Level) → Type _
SCwF ℓC ℓC' ℓT ℓT' =
  Σ[ C ∈ Category ℓC ℓC' ]
  Σ[ Ty ∈ Type ℓT ]
  Σ[ Tm ∈ (Ty → Presheaf C ℓT') ]
  Terminal' C ×
  -- "Simple comprehension"
  (∀ (Γ : C .ob) (A : Ty)
  → UniversalElement C (PshProd ⟅ (C [-, Γ ]) , (Tm A) ⟆b ))
