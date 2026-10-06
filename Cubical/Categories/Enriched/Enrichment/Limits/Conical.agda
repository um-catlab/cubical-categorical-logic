{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Enriched.Enrichment.Limits.Conical where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Limits.Conical
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Enrichment.HomFunctor
open import Cubical.Categories.Enriched.Enrichment.UniversalElement

private
  variable
    ℓV ℓV' ℓC ℓC' ℓJ ℓJ' : Level

module _ {V : MonoidalCategory ℓV ℓV'} {C : Category ℓC ℓC'} (ℰ : Enrichment C V) where

  EnrichedLimit : {J : Category ℓJ ℓJ'} (D : Functor J C) → Type _
  EnrichedLimit D = EnrichedUniversalElement ℰ
    (λ W → Cones (Hom[_,-] ℰ W ∘F D))
    (λ W → preservesCones (Hom[_,-] ℰ W) D)
