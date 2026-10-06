{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Enrichment.Functor.Base using (EnrichmentFor)

module Cubical.Categories.Enriched.Enrichment.Stage.Functor
  {ℓ ℓ' ℓS : Level} {A : Category ℓ ℓ'}
  {ℓC ℓC' ℓD ℓD' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {ℰC : Enrichment C (PshMon.𝓟Mon A ℓS)} {ℰD : Enrichment D (PshMon.𝓟Mon A ℓS)}
  {Fob : Category.ob C → Category.ob D}
  (E : EnrichmentFor (PshMon.𝓟Mon A ℓS) ℰC ℰD Fob) where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.StrictHom.Base
import Cubical.Categories.Enriched.Enrichment.Stage as Stage

open Functor
open PshHomStrict

private
  module A = Category A
  module E = EnrichmentFor E
  module SC = Stage ℰC
  module SD = Stage ℰD

stageF : ∀ c → Functor (SC.Stage c) (SD.Stage c)
stageF c .F-ob = Fob
stageF c .F-hom {X} {Y} = E.f[ X , Y ] .N-ob c
stageF c .F-id = funExt⁻ (funExt⁻ (cong N-ob E.fid) c) tt*
stageF c .F-seq α β = sym (funExt⁻ (funExt⁻ (cong N-ob E.f-seq) c) (α , β))

stageF-res : ∀ {c c'} (k : A [ c' , c ]) {X Y} (α : SC.Stage c [ X , Y ])
  → SD.res k ⟪ stageF c ⟪ α ⟫ ⟫ ≡ stageF c' ⟪ SC.res k ⟪ α ⟫ ⟫
stageF-res {c} {c'} k {X} {Y} α = E.f[ X , Y ] .N-hom c' c k α _ refl
