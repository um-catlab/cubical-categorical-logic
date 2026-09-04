{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Model where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝒱; r to 𝒞; ≤Vertex to ≤Kind)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Algebra
open import Cubical.Categories.Displayed.Instances.Algebra.Model
open import Cubical.Categories.Displayed.Instances.Reindex

open import Cubical.Algebra.Theory.Base
  hiding (ℓ; ℓᴰ; ℓᴰᴰ; ℓ'; ℓᴰ'; ℓᴰᴰ'; ℓ''; ℓᴰ''; ℓO; ℓA; ℓE)

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓO ℓA ℓE ℓEA : Level

open Categoryᴰ

module _ (C : CBPVCat ℓ ℓ') (T : Theory ℓO ℓA ℓE ℓEA) where
  open Theory T
  private module C = Fibers C

  ModelEnrichment : Type _
  ModelEnrichment =
    Σ[ ModelEff ∈ (∀ (A : C.ob[ 𝒱 ]) (B : C.ob[ 𝒞 ])
      → Categoryᴰ.ob[_] (MODELOver T ℓ')
          (C.Hom[ _ ][ A , B ] , Categoryᴰ.isSetHomᴰ C)) ]
    (∀ {A A'} (V : C.Hom[ _ ][ A , A' ]) B
      → isHomoSimpl (_ , ModelEff A' B .fst) (_ , ModelEff A B .fst)
          (λ M → V C.⋆ᴰ M))
    ×
    (∀ {B B'} (S : C.Hom[ _ ][ B , B' ]) A
      → isHomoSimpl (_ , ModelEff A B .fst) (_ , ModelEff A B' .fst)
          (λ M → M C.⋆ᴰ S))

  ModelEnrichmentModel : ModelEnrichment →
    ∀ (A : C.ob[ 𝒱 ]) (B : C.ob[ 𝒞 ]) → Model ℓ'
  ModelEnrichmentModel CModel A B .fst =
    C.Hom[ _ ][ A , B ] , CModel .fst A B .fst
  ModelEnrichmentModel CModel A B .snd .fst = CModel .fst A B .snd
  ModelEnrichmentModel CModel A B .snd .snd = Categoryᴰ.isSetHomᴰ C

module _ {C : CBPVCat ℓ ℓ'} (T : Theory ℓO ℓA ℓE ℓEA)
  (CModel : ModelEnrichment C T)
  (Cᴰ : CBPVCatᴰ C ℓᴰ ℓᴰ') where
  open Theory T
  private module C = Fibers C
  private module Cᴰ = Fibers Cᴰ

  ModelEnrichmentᴰ : Type _
  ModelEnrichmentᴰ =
    Σ[ ModelEffᴰ ∈ (∀ {A B}
      (Aᴰ : Cᴰ.ob[ _ , A ]) (Bᴰ : Cᴰ.ob[ _ , B ])
      → ModelᴰWithCarrier (ModelEnrichmentModel C T CModel A B)
          (λ M → Cᴰ.Hom[ _ , M ][ Aᴰ , Bᴰ ])) ]
    (∀ {A A' B}
      {Aᴰ : Cᴰ.ob[ _ , A ]} {Aᴰ' : Cᴰ.ob[ _ , A' ]}
      {Bᴰ : Cᴰ.ob[ _ , B ]} {V : _}
      (Vᴰ : Cᴰ.Hom[ _ , V ][ Aᴰ , Aᴰ' ])
      → isHomoᴰSimpl
          ((λ M → V C.⋆ᴰ M) , CModel .snd .fst V B)
          (_ , ModelEffᴰ Aᴰ' Bᴰ .fst) (_ , ModelEffᴰ Aᴰ Bᴰ .fst)
          (λ _ Mᴰ → Vᴰ Cᴰ.⋆ᴰ Mᴰ))
    ×
    (∀ {A B B'}
      {Aᴰ : Cᴰ.ob[ _ , A ]} {Bᴰ : Cᴰ.ob[ _ , B ]}
      {Bᴰ' : Cᴰ.ob[ _ , B' ]} {S : _}
      (Sᴰ : Cᴰ.Hom[ _ , S ][ Bᴰ , Bᴰ' ])
      → isHomoᴰSimpl
          ((λ M → M C.⋆ᴰ S) , CModel .snd .snd S A)
          (_ , ModelEffᴰ Aᴰ Bᴰ .fst) (_ , ModelEffᴰ Aᴰ Bᴰ' .fst)
          (λ _ Mᴰ → Mᴰ Cᴰ.⋆ᴰ Sᴰ))

module _ {C : CBPVCat ℓ ℓ'} {D : CBPVCat ℓD ℓD'}
  (T : Theory ℓO ℓA ℓE ℓEA)
  (F : Functorⱽ C D)
  (CModel : ModelEnrichment C T) (DModel : ModelEnrichment D T)
  where
  open Theory T

  PreservesModelEnrichment : Type _
  PreservesModelEnrichment = ∀ A B →
    isHomoSimpl (_ , CModel .fst A B .fst)
      (_ , DModel .fst
        (F .Functorᴰ.F-obᴰ A) (F .Functorᴰ.F-obᴰ B) .fst)
      (F .Functorᴰ.F-homᴰ)

module _
  {C : CBPVCat ℓ ℓ'} {D : CBPVCat ℓD ℓD'}
  (T : Theory ℓO ℓA ℓE ℓEA)
  (F : Functorⱽ C D)
  (CModel : ModelEnrichment C T) (DModel : ModelEnrichment D T)
  (FModel : PreservesModelEnrichment T F CModel DModel)
  (Dᴰ : CBPVCatᴰ D ℓCᴰ ℓCᴰ')
  (DᴰModel : ModelEnrichmentᴰ T DModel Dᴰ)
  where
  open Theory T
  private
    module C = Fibers C
    module D = Fibers D
    module Dᴰ = Fibers Dᴰ
    module F = Functorᴰ F

    CAlg : AlgebraEnrichment C S
    CAlg .fst A B = CModel .fst A B .fst
    CAlg .snd = CModel .snd

    DAlg : AlgebraEnrichment D S
    DAlg .fst A B = DModel .fst A B .fst
    DAlg .snd = DModel .snd

    FAlg : PreservesAlgebraEnrichment S F CAlg DAlg
    FAlg = FModel

    DᴰAlg : AlgebraEnrichmentᴰ S DAlg Dᴰ
    DᴰAlg .fst Aᴰ Bᴰ = DᴰModel .fst Aᴰ Bᴰ .fst
    DᴰAlg .snd = DᴰModel .snd

    F*Cᴰ = reindex Dᴰ (∫F F)
    module F*Cᴰ = Fibers F*Cᴰ

    FModelHomo : ∀ A B → Homo
      (ModelEnrichmentModel C T CModel A B .fst)
      (ModelEnrichmentModel D T DModel (F.F-obᴰ A) (F.F-obᴰ B) .fst)
    FModelHomo A B .fst = F.F-homᴰ
    FModelHomo A B .snd = FModel A B

    DᴰModelAt : ∀ {A : D.ob[ 𝒱 ]} {B : D.ob[ 𝒞 ]}
      (Aᴰ : Dᴰ.ob[ _ , A ]) (Bᴰ : Dᴰ.ob[ _ , B ])
      → Modelᴰ (ModelEnrichmentModel D T DModel A B) ℓCᴰ'
    DᴰModelAt Aᴰ Bᴰ .fst .fst M = Dᴰ.Hom[ _ , M ][ Aᴰ , Bᴰ ]
    DᴰModelAt Aᴰ Bᴰ .fst .snd = DᴰModel .fst Aᴰ Bᴰ .fst
    DᴰModelAt Aᴰ Bᴰ .snd .fst = DᴰModel .fst Aᴰ Bᴰ .snd
    DᴰModelAt Aᴰ Bᴰ .snd .snd _ = Categoryᴰ.isSetHomᴰ Dᴰ

    PulledModel : ∀ {A : C.ob[ 𝒱 ]} {B : C.ob[ 𝒞 ]}
      (Aᴰ : Dᴰ.ob[ _ , F.F-obᴰ A ]) (Bᴰ : Dᴰ.ob[ _ , F.F-obᴰ B ])
      → Modelᴰ (ModelEnrichmentModel C T CModel A B) ℓCᴰ'
    PulledModel {A} {B} Aᴰ Bᴰ =
      Theory._*_ T (FModelHomo A B) (DᴰModelAt Aᴰ Bᴰ)

    ModelEffᴰReindex : ∀ {A : C.ob[ 𝒱 ]} {B : C.ob[ 𝒞 ]}
      (Aᴰ : Dᴰ.ob[ _ , F.F-obᴰ A ]) (Bᴰ : Dᴰ.ob[ _ , F.F-obᴰ B ])
      → ModelᴰWithCarrier (ModelEnrichmentModel C T CModel A B)
          (λ M → F*Cᴰ.Hom[ _ , M ][ Aᴰ , Bᴰ ])
    ModelEffᴰReindex Aᴰ Bᴰ .fst = PulledModel Aᴰ Bᴰ .fst .snd
    ModelEffᴰReindex Aᴰ Bᴰ .snd = PulledModel Aᴰ Bᴰ .snd .fst

    AlgebraEnrichmentᴰReindexed : AlgebraEnrichmentᴰ S CAlg F*Cᴰ
    AlgebraEnrichmentᴰReindexed =
      AlgebraEnrichmentᴰReindex S F CAlg DAlg FAlg Dᴰ DᴰAlg

  ModelEnrichmentᴰReindex : ModelEnrichmentᴰ T CModel F*Cᴰ
  ModelEnrichmentᴰReindex .fst = ModelEffᴰReindex
  ModelEnrichmentᴰReindex .snd = AlgebraEnrichmentᴰReindexed .snd
