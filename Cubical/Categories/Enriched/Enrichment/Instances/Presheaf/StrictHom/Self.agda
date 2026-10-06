{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Enrichment.Instances.Self

module Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Self
  {ℓ ℓ' : Level} (A : Category ℓ ℓ') (ℓS : Level)
  where

open PshMon A ℓS

selfEnrichment : Enrichment 𝓟 𝓟Mon
selfEnrichment = leftSelfEnrichment 𝓟Mon 𝓟LeftClosed
