{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Functors.Currying
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.BinProduct.More
open import Cubical.Categories.Displayed.Instances.Functor
open import Cubical.Categories.Displayed.Instances.Terminal.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Base
import Cubical.Categories.Displayed.Instances.Terminal.Properties as Terminal
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Base

private
  variable
    ℓ ℓ' ℓD ℓE ℓE' ℓCᴰ ℓCᴰ' ℓEᴰᴰ ℓEᴰᴰ' : Level

UnitTotal : (D : Category ℓ ℓ') → Functor D (∫C (Unitᴰ D))
UnitTotal D = intro Id ttS

module _
  (C : CBPVCat ℓ ℓ')
  (Eᴰ : Categoryᴰ (SET ℓ') ℓE ℓE')
  where

  -- An enrichment of the Computation profunctor to some structure Eᴰ
  -- over SET.
  Enrichment : Type _
  Enrichment =
    Section
      (VCProf C)
      (FUNCTORᴰ (Unitᴰ (ValueCat C ^op)) Eᴰ)

  EnrichmentF : Enrichment → Functorᴰ
      (VCProf C)
      (Unitᴰ (ComputationCat C))
      (FUNCTORᴰ (Unitᴰ (ValueCat C ^op)) Eᴰ)
  EnrichmentF Cᴱ = Terminal.recᴰ Cᴱ

  EnrichedHomTotal : Enrichment → Functor
    (ComputationCat C)
    (FUNCTOR (ValueCat C ^op) (∫C Eᴰ))
  EnrichedHomTotal Cᴱ =
    precomposeF (∫C Eᴰ) (UnitTotal (ValueCat C ^op))
    ∘F ∫F-Functor (Unitᴰ (ValueCat C ^op)) Eᴰ
    ∘F ∫F (EnrichmentF Cᴱ)
    ∘F UnitTotal (ComputationCat C)

  EnrichedHomTotalᵘ : Enrichment → Functor
    (ComputationCat C ×C ValueCat C ^op)
    (∫C Eᴰ)
  EnrichedHomTotalᵘ Cᴱ =
    λF⁻ (ValueCat C ^op) (∫C Eᴰ) (ComputationCat C)
      (EnrichedHomTotal Cᴱ)

module _
  {C : CBPVCat ℓ ℓ'}
  {D : CBPVCat ℓD ℓ'}
  (Eᴰ : Categoryᴰ (SET ℓ') ℓE ℓE')
  (F : Functorⱽ C D)
  (Cᴱ : Enrichment C Eᴰ)
  (Dᴱ : Enrichment D Eᴰ)
  where
  private
    UnitValueFᴰ : Functorᴰ
      (ValueF F ^opF)
      (Unitᴰ (ValueCat C ^op))
      (Unitᴰ (ValueCat D ^op))
    UnitValueFᴰ = Terminal.introF (ValueF F ^opF)

    UnitComputationFᴰ : Functorᴰ
      (ComputationF F)
      (Unitᴰ (ComputationCat C))
      (Unitᴰ (ComputationCat D))
    UnitComputationFᴰ = Terminal.introF (ComputationF F)

    DᴱReindex : Functorᴰ
      (VCProfReindex F)
      (Unitᴰ (ComputationCat C))
      (FUNCTORᴰ (Unitᴰ (ValueCat C ^op)) Eᴰ)
    DᴱReindex =
      precomposeFᴰ (SET ℓ') Eᴰ UnitValueFᴰ
      ∘Fᴰ (EnrichmentF D Eᴰ Dᴱ ∘Fᴰ UnitComputationFᴰ)

  PreservesEnrichment : Type _
  PreservesEnrichment =
    NatTransᴰ
      (VCProfNatTrans F)
      (EnrichmentF C Eᴰ Cᴱ)
      DᴱReindex

  EnrichedHomTotalReindex : Functor
    (ComputationCat C)
    (FUNCTOR (ValueCat C ^op) (∫C Eᴰ))
  EnrichedHomTotalReindex =
    precomposeF (∫C Eᴰ) (ValueF F ^opF)
    ∘F EnrichedHomTotal D Eᴰ Dᴱ
    ∘F ComputationF F

  EnrichedHomTotalNatTrans :
    (Fᴱ : PreservesEnrichment) → NatTrans
      (EnrichedHomTotal C Eᴰ Cᴱ)
      EnrichedHomTotalReindex
  EnrichedHomTotalNatTrans Fᴱ .NatTrans.N-ob B .NatTrans.N-ob A =
    (VCProfNatTrans F .NatTrans.N-ob B .NatTrans.N-ob A) ,
    (Fᴱ .NatTransᴰ.N-obᴰ tt .NatTransᴰ.N-obᴰ tt)
  EnrichedHomTotalNatTrans Fᴱ .NatTrans.N-ob B .NatTrans.N-hom V =
    ΣPathP
      (VCProfNatTrans F .NatTrans.N-ob B .NatTrans.N-hom V
      , Fᴱ .NatTransᴰ.N-obᴰ tt .NatTransᴰ.N-homᴰ tt)
  EnrichedHomTotalNatTrans Fᴱ .NatTrans.N-hom S =
    makeNatTransPath (funExt λ A → ΣPathP
      ((λ i → (VCProfNatTrans F .NatTrans.N-hom S i) .NatTrans.N-ob A)
      , (λ i → (Fᴱ .NatTransᴰ.N-homᴰ tt i) .NatTransᴰ.N-obᴰ tt)))

  EnrichedHomTotalReindexᵘ : Functor
    (ComputationCat C ×C ValueCat C ^op)
    (∫C Eᴰ)
  EnrichedHomTotalReindexᵘ =
    λF⁻ (ValueCat C ^op) (∫C Eᴰ) (ComputationCat C)
      EnrichedHomTotalReindex

  EnrichedHomTotalNatTransᵘ :
    (Fᴱ : PreservesEnrichment) → NatTrans
      (EnrichedHomTotalᵘ C Eᴰ Cᴱ)
      EnrichedHomTotalReindexᵘ
  EnrichedHomTotalNatTransᵘ Fᴱ =
    (λF⁻Functor (ValueCat C ^op) (∫C Eᴰ) (ComputationCat C))
      .Functor.F-hom (EnrichedHomTotalNatTrans Fᴱ)

module _
  (C : CBPVCat ℓ ℓ')
  (D : CBPVCat ℓD ℓ')
  (Eᴰ : Categoryᴰ (SET ℓ') ℓE ℓE')
  (Cᴱ : Enrichment C Eᴰ)
  (Dᴱ : Enrichment D Eᴰ)
  where

  EnrichedFunctor : Type _
  EnrichedFunctor =
    Σ[ F ∈ Functorⱽ C D ] PreservesEnrichment Eᴰ F Cᴱ Dᴱ

module _
  {C : CBPVCat ℓ ℓ'}
  (Eᴰ : Categoryᴰ (SET ℓ') ℓE ℓE')
  (Cᴱ : Enrichment C Eᴰ)
  (Cᴰ : CBPVCatᴰ C ℓCᴰ ℓCᴰ')
  (Eᴰᴰ : Categoryᴰ (∫C Eᴰ) ℓEᴰᴰ ℓEᴰᴰ')
  where
  Enrichmentᴰ : Type _
  Enrichmentᴰ =
    Functorᴰ
      (EnrichedHomTotalᵘ C Eᴰ Cᴱ)
      (ComputationCatᴰ Cᴰ ×Cᴰ ((ValueCatᴰ Cᴰ) ^opᴰ))
      Eᴰᴰ

  EnrichmentᴰFibration : Type _
  EnrichmentᴰFibration = EqFibrationData
    (FUNCTORᴰ
      (ComputationCatᴰ Cᴰ ×Cᴰ ((ValueCatᴰ Cᴰ) ^opᴰ))
      Eᴰᴰ)

  EnrichmentᴰFibrationFrom :
    EqFibrationData Eᴰᴰ → EnrichmentᴰFibration
  EnrichmentᴰFibrationFrom =
    FUNCTORᴰ-FibrationEq
      (ComputationCatᴰ Cᴰ ×Cᴰ ((ValueCatᴰ Cᴰ) ^opᴰ)) Eᴰᴰ

module _
  {C : CBPVCat ℓ ℓ'} {D : CBPVCat ℓD ℓ'}
  (Eᴰ : Categoryᴰ (SET ℓ') ℓE ℓE')
  (F : Functorⱽ C D)
  (Cᴱ : Enrichment C Eᴰ) (Dᴱ : Enrichment D Eᴰ)
  (Fᴱ : PreservesEnrichment Eᴰ F Cᴱ Dᴱ)
  (Dᴰ : CBPVCatᴰ D ℓCᴰ ℓCᴰ')
  (Eᴰᴰ : Categoryᴰ (∫C Eᴰ) ℓEᴰᴰ ℓEᴰᴰ')
  (Dᴱᴰ : Enrichmentᴰ Eᴰ Dᴱ Dᴰ Eᴰᴰ)
  where
  private
    F*Dᴰ : CBPVCatᴰ C ℓCᴰ ℓCᴰ'
    F*Dᴰ = reindex Dᴰ (∫F F)

    DᴱᴰReindex : Functorᴰ
      (EnrichedHomTotalReindexᵘ Eᴰ F Cᴱ Dᴱ)
      (ComputationCatᴰ F*Dᴰ ×Cᴰ ((ValueCatᴰ F*Dᴰ) ^opᴰ))
      Eᴰᴰ
    DᴱᴰReindex =
      reindF'
        (EnrichedHomTotalReindexᵘ Eᴰ F Cᴱ Dᴱ)
        Eq.refl Eq.refl
        (Dᴱᴰ ∘Fᴰ
          (ComputationFᴰ F Dᴰ ×Fᴰ ((ValueFᴰ F Dᴰ) ^opFᴰ)))

  EnrichmentᴰReindex :
    EqFibrationData Eᴰᴰ →
    Enrichmentᴰ Eᴰ Cᴱ F*Dᴰ Eᴰᴰ
  EnrichmentᴰReindex isFib =
    ((EnrichmentᴰFibrationFrom Eᴰ Cᴱ F*Dᴰ Eᴰᴰ isFib)
      .Eq-fibration
        (EnrichedHomTotalNatTransᵘ Eᴰ F Cᴱ Dᴱ Fᴱ)
        DᴱᴰReindex)
      .fst

  private
    check-EnrichmentᴰReindex :
      EqFibrationData Eᴰᴰ →
      Enrichmentᴰ Eᴰ Cᴱ F*Dᴰ Eᴰᴰ
    check-EnrichmentᴰReindex = EnrichmentᴰReindex
