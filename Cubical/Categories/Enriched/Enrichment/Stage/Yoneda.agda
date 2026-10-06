{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

module Cubical.Categories.Enriched.Enrichment.Stage.Yoneda
  {ℓ ℓ' : Level} (A : Category ℓ ℓ') (ℓS : Level) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.Constructions.Lift
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom

open Functor
open PshHomStrict
open PshMon A ℓS using (𝓟 ; ℓm)

private
  module A = Category A

ŷ : A.ob → Presheaf A ℓm
ŷ c = LiftPsh (YOStrict {C = A} ⟅ c ⟆) ℓm

module _ (c : A.ob) (H : Presheaf A ℓm) where
  yoneda : Iso (𝓟 [ ŷ c , H ]) ⟨ H .F-ob c ⟩
  yoneda .Iso.fun α = α .N-ob c (lift A.id)
  yoneda .Iso.inv h .N-ob d (lift g) = H .F-hom g h
  yoneda .Iso.inv h .N-hom d' d k (lift g) (lift g') e =
    sym (funExt⁻ (H .F-seq g k) h) ∙ cong (λ m → H .F-hom (m .lower) h) e
  yoneda .Iso.sec h = funExt⁻ (H .F-id) h
  yoneda .Iso.ret α = makePshHomStrictPath (funExt λ d → funExt λ (lift g) →
    α .N-hom d c g (lift A.id) (lift g) (cong lift (A.⋆IdR g)))
