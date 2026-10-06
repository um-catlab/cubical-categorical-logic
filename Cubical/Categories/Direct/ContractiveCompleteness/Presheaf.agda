{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
module Cubical.Categories.Direct.ContractiveCompleteness.Presheaf
  {ℓ ℓ' ℓD : Level} {A : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'}
  (dir : DirectStr A Wo) where

open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Displayed.Instances.FunctorAlgebras using (InitialAlgebra)
open import Cubical.Categories.Displayed.Instances.FunctorCoalgebras using (TerminalCoalgebra)
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive
open import Cubical.Categories.Enriched.Enrichment.Limits.Power using (EnrichedPower)
open import Cubical.Categories.Enriched.Enrichment.Limits.Conical using (EnrichedLimit)
open import Cubical.Categories.Enriched.Enrichment.Stage.Yoneda A ℓ using (ŷ)
open import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Self A ℓ
  using (selfEnrichment)
import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Power A ℓ as Power
import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Conical as Conical
open import Cubical.Categories.Direct.Guarded.Presheaf dir using (pshGuarded)
import Cubical.Categories.Direct.ContractiveCompleteness dir as CC

open PshMon A ℓ using (𝓟)

module _ (F : Functor 𝓟 𝓟) (lc : isLocallyContractive pshGuarded selfEnrichment selfEnrichment F) where
  private
    pws : ∀ z X → EnrichedPower selfEnrichment (ŷ z) X
    pws z X = Power.pshPower (ŷ z) X

    lims : ∀ (S : A .Category.ob → Type ℓ') (D : Functor (FullSubcategory A S ^op) 𝓟)
      → EnrichedLimit selfEnrichment D
    lims S D = Conical.pshLimit A (FullSubcategory A S ^op) ℓ D

  pshInitialAlgebra : InitialAlgebra F
  pshInitialAlgebra = CC.initialAlgebra selfEnrichment F lc pws lims

  pshTerminalCoalgebra : TerminalCoalgebra F
  pshTerminalCoalgebra = CC.terminalCoalgebra selfEnrichment F lc pws lims
