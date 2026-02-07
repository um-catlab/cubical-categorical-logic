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
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable.More

open Category

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level
record SCwF (ℓC ℓC' ℓT ℓT' : Level) : Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓT ℓT'))) where
  no-eta-equality
  field
    C : Category ℓC ℓC'
    Ty : Type ℓT
    Tm : Ty → Presheaf C ℓT'
    term : Terminal' C
    -- "Simple comprehension"
    comprehension : ∀ A → LocallyRepresentable (Tm A)
  module C = Category C
  module Tm⟨_⟩ (A : Ty) = PresheafNotation (Tm A)
  module term = TerminalNotation term
  ext = comprehension
  module ext (Γ : C.ob)(A : Ty) = UniversalElementNotation (ext A Γ)
