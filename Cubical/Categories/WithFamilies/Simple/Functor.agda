{- Functors of SCwFs. These come in variants depending on whether the extension is preserved. -}
module Cubical.Categories.WithFamilies.Simple.Functor where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.WithFamilies.Simple.Base

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

module _ (C : SCwF ℓC ℓC' ℓT ℓT')(D : SCwF ℓD ℓD' ℓS ℓS') where
  private
    module C = SCwF C
    module D = SCwF D
  -- A PreFunctor is not required to preserve the terminal ctx or comprehensions
  PreFunctor : Type _
  PreFunctor =
    Σ[ F ∈ Functor C.C D.C ]
    Σ[ F-ty ∈ (C.Ty → D.Ty) ]
    ∀ {A} → PshHet F (C.Tm A) (D.Tm (F-ty A))
