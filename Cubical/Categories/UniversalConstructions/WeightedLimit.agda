{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.UniversalConstructions.WeightedLimit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Monoidal.Closed using (_⊗-)
open import Cubical.Categories.Monoidal.Instances.Sets using (SETMon)
open import Cubical.Categories.Enriched.Enrichment.HomFunctor
open import Cubical.Categories.Enriched.Enrichment.Instances.Sets
open import Cubical.Categories.Enriched.Enrichment.Limits.Weighted

private
  variable
    ℓC ℓC' ℓK ℓK' : Level

open NatTrans

module _ {C : Category ℓC ℓC'} {K : Category ℓK ℓK'}
  (D : Functor K C) (W : Functor K (SET ℓC')) where

  WeightedLimit : Type _
  WeightedLimit = UniversalElement C (WeightedCones (SET-Enrichment C) W D)

  WeightedLimit→EnrichedWeightedLimit : WeightedLimit → EnrichedWeightedLimit (SET-Enrichment C) W D
  WeightedLimit→EnrichedWeightedLimit ue .fst = ue
  WeightedLimit→EnrichedWeightedLimit ue .snd X U = isoToIsEquiv (iso _ inv
    (λ t → makeNatTransPath (funExt λ j → funExt λ (u , w) →
      cong (λ q → q .N-ob j w) ue.β))
    (λ h → funExt λ u → cong ue.intro (makeNatTransPath refl) ∙ sym ue.η))
    where
    module ue = UniversalElementNotation ue
    inv : NatTrans (_⊗- SETMon U ∘F W) (Hom[_,-] (SET-Enrichment C) X ∘F D)
      → ⟨ U ⟩ → C [ X , ue.vertex ]
    inv t u = ue.intro (natTrans (λ j w → t .N-ob j (u , w)) (λ k → funExt λ w → funExt⁻ (t .N-hom k) (u , w)))
