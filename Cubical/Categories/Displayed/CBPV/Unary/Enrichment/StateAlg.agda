-- The state algebra enrichment of a CBPV category is an instance of
-- the abstract notion of enrichment: an Enrichment in state algebras
-- displayed over SET. Likewise a displayed state algebra enrichment
-- is an Enrichmentᴰ in displayed state algebras, which form a
-- fibration, so the abstract reindexing theorem applies.
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Enrichment.StateAlg where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Functor.Properties
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.StateAlg
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Base
open import Cubical.Categories.Displayed.CBPV.Unary.StateAlgEnrichment

open import Cubical.Algebra.State

private
  variable
    ℓ ℓ' ℓD ℓᴰ ℓᴰ' : Level

module _ {C : CBPVCat ℓ ℓ'} where
  StateAlgEnrichment→Enrichment :
    StateAlgEnrichment C → Enrichment C (STATEALGOver ℓ')
  StateAlgEnrichment→Enrichment CState =
    mkPropHomsSection (hasPropHomsFUNCTORᴰ hasPropHomsSTATEALGOver)
      (λ B → mkPropHomsFunctor hasPropHomsSTATEALGOver
        (λ {A} _ → CState .fst A B)
        (λ {A'} {A} {V} _ → CState .snd .fst V B))
      (λ S → mkPropHomsNatTransᴰ hasPropHomsSTATEALGOver
        (λ {A} _ → CState .snd .snd S A))

  Enrichment→StateAlgEnrichment :
    Enrichment C (STATEALGOver ℓ') → StateAlgEnrichment C
  Enrichment→StateAlgEnrichment Cᴱ .fst A B =
    Cᴱ .Section.F-obᴰ B .Functorᴰ.F-obᴰ _
  Enrichment→StateAlgEnrichment Cᴱ .snd .fst V B =
    Cᴱ .Section.F-obᴰ B .Functorᴰ.F-homᴰ _
  Enrichment→StateAlgEnrichment Cᴱ .snd .snd S A =
    Cᴱ .Section.F-homᴰ S .NatTransᴰ.N-obᴰ _

module _ {C : CBPVCat ℓ ℓ'} {D : CBPVCat ℓD ℓ'}
  (F : Functorⱽ C D)
  (CState : StateAlgEnrichment C) (DState : StateAlgEnrichment D)
  where
  PreservesStateAlgEnrichment→PreservesEnrichment :
    PreservesStateAlgEnrichment F CState DState
    → PreservesEnrichment (STATEALGOver ℓ') F
        (StateAlgEnrichment→Enrichment CState)
        (StateAlgEnrichment→Enrichment DState)
  PreservesStateAlgEnrichment→PreservesEnrichment FState =
    mkPropHomsNatTransᴰ (hasPropHomsFUNCTORᴰ hasPropHomsSTATEALGOver)
      (λ {B} _ → mkPropHomsNatTransᴰ hasPropHomsSTATEALGOver
        (λ {A} _ → FState A B))

  PreservesEnrichment→PreservesStateAlgEnrichment :
    PreservesEnrichment (STATEALGOver ℓ') F
        (StateAlgEnrichment→Enrichment CState)
        (StateAlgEnrichment→Enrichment DState)
    → PreservesStateAlgEnrichment F CState DState
  PreservesEnrichment→PreservesStateAlgEnrichment Fᴱ A B =
    Fᴱ .NatTransᴰ.N-obᴰ _ .NatTransᴰ.N-obᴰ _

-- A displayed state algebra enrichment is a displayed enrichment in
-- displayed state algebras over the total category of state algebras.
module _ {C : CBPVCat ℓ ℓ'} (CState : StateAlgEnrichment C)
  (Cᴰ : CBPVCatᴰ C ℓᴰ ℓᴰ') where
  private
    module Cᴰ = Fibers Cᴰ
    Hᵘ = EnrichedHomTotalᵘ C (STATEALGOver ℓ')
      (StateAlgEnrichment→Enrichment CState)
  open Functorᴰ

  StateAlgEnrichmentᴰ→Enrichmentᴰ :
    StateAlgEnrichmentᴰ CState Cᴰ
    → Enrichmentᴰ (STATEALGOver ℓ')
        (StateAlgEnrichment→Enrichment CState) Cᴰ (STATEALGᴰ ℓ' ℓᴰ')
  StateAlgEnrichmentᴰ→Enrichmentᴰ CStateᴰ .F-obᴰ (Bᴰ , Aᴰ) .fst M =
    Cᴰ.Hom[ _ , M ][ Aᴰ , Bᴰ ] , Cᴰ.isSetHomᴰ
  StateAlgEnrichmentᴰ→Enrichmentᴰ CStateᴰ .F-obᴰ (Bᴰ , Aᴰ) .snd =
    CStateᴰ .fst Aᴰ Bᴰ
  StateAlgEnrichmentᴰ→Enrichmentᴰ CStateᴰ .F-homᴰ (Sᴰ , Vᴰ) .fst M Mᴰ =
    (Vᴰ Cᴰ.⋆ᴰ Mᴰ) Cᴰ.⋆ᴰ Sᴰ
  StateAlgEnrichmentᴰ→Enrichmentᴰ CStateᴰ .F-homᴰ (Sᴰ , Vᴰ) .snd =
    CStateᴰ .snd .fst Vᴰ ⋆Homoᴰ CStateᴰ .snd .snd Sᴰ
  StateAlgEnrichmentᴰ→Enrichmentᴰ CStateᴰ .F-idᴰ {x = B , A} = ΣPathP
    ( (λ i M Mᴰ → Cᴰ.rectifyOut
        {e' = λ j → _ , Hᵘ .Functor.F-id {B , A} j .fst M}
        (Cᴰ.⟨ Cᴰ.⟨ Cᴰ.reind-revealed-filler⁻ {p = Cᴰ.idᴰ}
                 (sym (ValueIncl C .Functor.F-id))
               ⟩⋆⟨ refl {x = _ , Mᴰ} ⟩
          ⟩⋆⟨ Cᴰ.reind-revealed-filler⁻ {p = Cᴰ.idᴰ}
                 (sym (ComputationIncl C .Functor.F-id)) ⟩
        ∙ Cᴰ.⟨ Cᴰ.⋆IdL (_ , Mᴰ) ⟩⋆⟨ refl {x = _ , Cᴰ.idᴰ} ⟩
        ∙ Cᴰ.⋆IdR (_ , Mᴰ)) i)
    , isProp→PathP (λ i → isPropHomoᴰ (λ _ → Cᴰ.isSetHomᴰ)) _ _)
  StateAlgEnrichmentᴰ→Enrichmentᴰ CStateᴰ .F-seqᴰ
    {f = S , V} {g = S' , V'} (Sᴰ , Vᴰ) (Sᴰ' , Vᴰ') =
    ΣPathP
    ( (λ i M Mᴰ → Cᴰ.rectifyOut
        {e' = λ j → _ , Hᵘ .Functor.F-seq (S , V) (S' , V') j .fst M}
        (Cᴰ.⟨ Cᴰ.⟨ Cᴰ.reind-revealed-filler⁻ {p = Vᴰ' Cᴰ.⋆ᴰ Vᴰ}
                 (sym (ValueIncl C .Functor.F-seq V' V))
               ⟩⋆⟨ refl {x = _ , Mᴰ} ⟩
          ⟩⋆⟨ Cᴰ.reind-revealed-filler⁻ {p = Sᴰ Cᴰ.⋆ᴰ Sᴰ'}
                 (sym (ComputationIncl C .Functor.F-seq S S')) ⟩
        ∙ Cᴰ.⟨ Cᴰ.⋆Assoc (_ , Vᴰ') (_ , Vᴰ) (_ , Mᴰ)
          ⟩⋆⟨ refl {x = _ , Sᴰ Cᴰ.⋆ᴰ Sᴰ'} ⟩
        ∙ sym (Cᴰ.⋆Assoc (_ , Vᴰ' Cᴰ.⋆ᴰ (Vᴰ Cᴰ.⋆ᴰ Mᴰ)) (_ , Sᴰ) (_ , Sᴰ'))
        ∙ Cᴰ.⟨ Cᴰ.⋆Assoc (_ , Vᴰ') (_ , Vᴰ Cᴰ.⋆ᴰ Mᴰ) (_ , Sᴰ)
          ⟩⋆⟨ refl {x = _ , Sᴰ'} ⟩) i)
    , isProp→PathP (λ i → isPropHomoᴰ (λ _ → Cᴰ.isSetHomᴰ)) _ _)

-- The abstract reindexing theorem, instantiated to state algebras.
module _ {C : CBPVCat ℓ ℓ'} {D : CBPVCat ℓD ℓ'}
  (F : Functorⱽ C D)
  (CState : StateAlgEnrichment C) (DState : StateAlgEnrichment D)
  (FState : PreservesStateAlgEnrichment F CState DState)
  (Dᴰ : CBPVCatᴰ D ℓᴰ ℓ')
  (DᴰState : StateAlgEnrichmentᴰ DState Dᴰ)
  where
  EnrichmentᴰReindexStateAlg :
    Enrichmentᴰ (STATEALGOver ℓ')
      (StateAlgEnrichment→Enrichment CState)
      (reindex Dᴰ (∫F F))
      (STATEALGᴰ ℓ' ℓ')
  EnrichmentᴰReindexStateAlg =
    EnrichmentᴰReindex (STATEALGOver ℓ') F
      (StateAlgEnrichment→Enrichment CState)
      (StateAlgEnrichment→Enrichment DState)
      (PreservesStateAlgEnrichment→PreservesEnrichment F CState DState FState)
      Dᴰ (STATEALGᴰ ℓ' ℓ')
      (StateAlgEnrichmentᴰ→Enrichmentᴰ DState Dᴰ DᴰState)
      (StateAlgᴰEqFibrationData ℓ')
