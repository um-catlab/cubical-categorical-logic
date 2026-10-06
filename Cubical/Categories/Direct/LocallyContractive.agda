{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
module Cubical.Categories.Direct.LocallyContractive
  {ℓ ℓ' ℓD : Level} {A : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'} (dir : DirectStr A Wo) where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Functor using (Functor ; _∘F_)
import Cubical.Categories.Presheaf.Family.Base as FamBase
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.BinProduct using (_×Psh_)
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Direct.StrictDownset dir
open import Cubical.Categories.Displayed.Instances.FunctorAlgebras.Recursive
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.Instances.Presheaf.StrictHom.Self

open import Cubical.Categories.Enriched.Enrichment.Base
  renaming (Enrichment to VE)
open import Cubical.Categories.Enriched.Enrichment.Functor.Base
open import Cubical.Categories.Direct.Guarded.Presheaf dir using (pshGuarded)
import Cubical.Categories.Enriched.Enrichment.LocallyContractive as EnrLC

open import Cubical.Categories.Monoidal.Base


open DirectNotation dir using (_≺_)

module _
  {ℓC ℓC' ℓD ℓD' ℓO : Level}
  {Wo : WFOrder ℓO ℓ'}
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (ℰC : VE C (PshMon.𝓟Mon A ℓ))
  (ℰD : VE D (PshMon.𝓟Mon A ℓ))
  (F : Functor C D)
  where
    isLocallyContractive : Type _
    isLocallyContractive = EnrLC.isLocallyContractive pshGuarded ℰC ℰD F
