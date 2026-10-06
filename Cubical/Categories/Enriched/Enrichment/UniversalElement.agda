{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Enriched.Enrichment.UniversalElement where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Enrichment.HomFunctor

private
  variable
    ℓV ℓV' ℓC ℓC' ℓP ℓQ : Level

module _ {V : MonoidalCategory ℓV ℓV'} {C : Category ℓC ℓC'} (ℰ : Enrichment C V)
  {P : Presheaf C ℓP} (Q : Category.ob C → Presheaf (MonoidalCategory.C V) ℓQ)
  (α : ∀ W → PshHet (Hom[_,-] ℰ W) P (Q W)) where

  EnrichedUniversalElement : Type _
  EnrichedUniversalElement =
    Σ[ ue ∈ UniversalElement C P ] (∀ W → preservesUniversalElement (α W) ue)
