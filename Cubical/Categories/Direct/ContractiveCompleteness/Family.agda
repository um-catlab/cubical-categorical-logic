{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
module Cubical.Categories.Direct.ContractiveCompleteness.Family
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
open import Cubical.Categories.Enriched.Enrichment.Instances.Power using (Setᴬ)
open import Cubical.Categories.Enriched.Enrichment.Instances.Family.Limits A ℓ using (famEnrichment)
import Cubical.Categories.Enriched.Enrichment.Instances.Family.Power A ℓ as Power
import Cubical.Categories.Enriched.Enrichment.Instances.Family.Conical as Conical
open import Cubical.Categories.Direct.Guarded.Presheaf dir using (pshGuarded)
import Cubical.Categories.Direct.ContractiveCompleteness dir as CC

open PshMon A ℓ using (ℓm)

private
  Fam = Setᴬ (A .Category.ob) ℓm

module _ (F : Functor Fam Fam) (lc : isLocallyContractive pshGuarded famEnrichment famEnrichment F) where
  private
    pws : ∀ z X → EnrichedPower famEnrichment (ŷ z) X
    pws z X = Power.famPower (ŷ z) X

    lims : ∀ (S : A .Category.ob → Type ℓ') (D : Functor (FullSubcategory A S ^op) Fam)
      → EnrichedLimit famEnrichment D
    lims S D = Conical.famLimit A (FullSubcategory A S ^op) ℓ D

  famInitialAlgebra : InitialAlgebra F
  famInitialAlgebra = CC.initialAlgebra famEnrichment F lc pws lims

  famTerminalCoalgebra : TerminalCoalgebra F
  famTerminalCoalgebra = CC.terminalCoalgebra famEnrichment F lc pws lims
