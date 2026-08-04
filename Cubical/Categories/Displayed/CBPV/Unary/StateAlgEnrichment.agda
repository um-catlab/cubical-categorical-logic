-- Enrichment of a CBPV in state algebras.

-- All of these definitions and constructions should generalize to an
-- arbitrary algebraic theory.

-- A CBPV model is state-enriched when its Hom profunctor extends to a
-- profunctor valued in StateAlg. For now at least we define this
-- manually, but it could be stated in those terms if state algebras
-- were defined as a displayed category over sets.

-- We define a displayed version in the obvious way. The most
-- important theorem is the reindexing theorem which says that a
-- displayed state enriched model can be reindexed along an enriched
-- functor. For now this theorem is very ugly and manual. Maybe we can
-- make it easier if we leverage the fact that state algebras can be
-- define as product-preserving functors (i.e., models of a Lawvere
-- theory)?
{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.CBPV.Unary.StateAlgEnrichment where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.More

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝒱; r to 𝒞; ≤Vertex to ≤Kind)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Algebra.State

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

open Category hiding (_∘_)
open Categoryᴰ
open Functor

module _ (C : CBPVCat ℓ ℓ') where
  private module C = Fibers C

  StateAlgEnrichment : Type _
  StateAlgEnrichment =
    Σ[ StateAlgEff ∈ (∀ (A : C.ob[ 𝒱 ]) (B : C.ob[ 𝒞 ])
      → StateAlg (C.Hom[ _ ][ A , B ])) ]
    (∀ {A A'} (V : C.Hom[ _ ][ A , A' ]) B
      → Homo (λ M → V C.⋆ᴰ M) (StateAlgEff A' B) (StateAlgEff A B))
    ×
    (∀ {B B'} (S : C.Hom[ _ ][ B , B' ]) A
      → Homo (λ M → M C.⋆ᴰ S) (StateAlgEff A B) (StateAlgEff A B'))

module _ {C : CBPVCat ℓ ℓ'}
  (CState : StateAlgEnrichment C)
  (Cᴰ : CBPVCatᴰ C ℓᴰ ℓᴰ') where
  private module Cᴰ = Fibers Cᴰ

  StateAlgEnrichmentᴰ : Type _
  StateAlgEnrichmentᴰ =
    Σ[ StateAlgEffᴰ ∈ (∀ {A B}
      (Aᴰ : Cᴰ.ob[ _ , A ]) (Bᴰ : Cᴰ.ob[ _ , B ])
      → StateAlgᴰ (CState .fst A B)
          (λ M → Cᴰ.Hom[ _ , M ][ Aᴰ , Bᴰ ])) ]
    (∀ {A A' B}
      {Aᴰ : Cᴰ.ob[ _ , A ]} {Aᴰ' : Cᴰ.ob[ _ , A' ]}
      {Bᴰ : Cᴰ.ob[ _ , B ]} {V : _}
      (Vᴰ : Cᴰ.Hom[ _ , V ][ Aᴰ , Aᴰ' ])
      → Homoᴰ (λ _ → Vᴰ Cᴰ.⋆ᴰ_)
          (CState .snd .fst V B)
          (StateAlgEffᴰ Aᴰ' Bᴰ) (StateAlgEffᴰ Aᴰ Bᴰ))
    ×
    (∀ {A B B'}
      {Aᴰ : Cᴰ.ob[ _ , A ]} {Bᴰ : Cᴰ.ob[ _ , B ]}
      {Bᴰ' : Cᴰ.ob[ _ , B' ]} {S : _}
      (Sᴰ : Cᴰ.Hom[ _ , S ][ Bᴰ , Bᴰ' ])
      → Homoᴰ (λ a → Cᴰ._⋆ᴰ Sᴰ)
          (CState .snd .snd S A)
          (StateAlgEffᴰ Aᴰ Bᴰ) (StateAlgEffᴰ Aᴰ Bᴰ'))

module _
  {C : CBPVCat ℓ ℓ'} {D : CBPVCat ℓD ℓD'}
  (F : Functorⱽ C D)
  (CState : StateAlgEnrichment C) (DState : StateAlgEnrichment D)
  where
  PreservesStateAlgEnrichment : Type _
  PreservesStateAlgEnrichment = ∀ A B →
    Homo (F .Functorᴰ.F-homᴰ)
      (CState .fst A B)
      (DState .fst (F .Functorᴰ.F-obᴰ A) (F .Functorᴰ.F-obᴰ B))

module _
  {C : CBPVCat ℓ ℓ'} {D : CBPVCat ℓD ℓD'}
  (F : Functorⱽ C D)
  (CState : StateAlgEnrichment C) (DState : StateAlgEnrichment D)
  (FState : PreservesStateAlgEnrichment F CState DState)
  (Dᴰ : CBPVCatᴰ D ℓCᴰ ℓCᴰ')
  (DᴰState : StateAlgEnrichmentᴰ DState Dᴰ)
  where
  private
    module C = Fibers C
    module D = Fibers D
    module Dᴰ = Fibers Dᴰ
    module F = Functorᴰ F

    F*Cᴰ = reindex Dᴰ (∫F F)
    module F*Cᴰ = Fibers F*Cᴰ

    isSetDHom : ∀ {A : D.ob[ 𝒱 ]} {B : D.ob[ 𝒞 ]}
      → isSet (D.Hom[ _ ][ A , B ])
    isSetDHom = Categoryᴰ.isSetHomᴰ D

    StateAlgEffᴰReindex : ∀ {A : C.ob[ 𝒱 ]} {B : C.ob[ 𝒞 ]}
      (Aᴰ : Dᴰ.ob[ _ , F.F-obᴰ A ]) (Bᴰ : Dᴰ.ob[ _ , F.F-obᴰ B ])
      → StateAlgᴰ (CState .fst A B)
          (λ M → F*Cᴰ.Hom[ _ , M ][ Aᴰ , Bᴰ ])
    StateAlgEffᴰReindex {A} {B} Aᴰ Bᴰ =
      reindexStateAlgᴰ (FState A B) (DᴰState .fst Aᴰ Bᴰ) isSetDHom

    state-subst-filler : ∀
      {A A' : C.ob[ 𝒱 ]} {B : C.ob[ 𝒞 ]}
      {Aᴰ : Dᴰ.ob[ _ , F.F-obᴰ A ]} {Aᴰ' : Dᴰ.ob[ _ , F.F-obᴰ A' ]}
      {Bᴰ : Dᴰ.ob[ _ , F.F-obᴰ B ]}
      {V : C.Hom[ _ ][ A , A' ]} {M : C.Hom[ _ ][ A' , B ]}
      (Vᴰ : Dᴰ.Hom[ _ , F.F-homᴰ V ][ Aᴰ , Aᴰ' ])
      (Mᴰ : Dᴰ.Hom[ _ , F.F-homᴰ M ][ Aᴰ' , Bᴰ ])
      → Path
          (Σ[ N ∈ D.Hom[ _ ][ F.F-obᴰ A , F.F-obᴰ B ] ]
            Dᴰ.Hom[ _ , N ][ Aᴰ , Bᴰ ])
          (F.F-homᴰ (V C.⋆ᴰ M) , Vᴰ F*Cᴰ.⋆ᴰ Mᴰ)
          (F.F-homᴰ V D.⋆ᴰ F.F-homᴰ M , Vᴰ Dᴰ.⋆ᴰ Mᴰ)
    state-subst-filler {V = V} {M = M} Vᴰ Mᴰ i .fst =
      sym (Dᴰ.reind-revealed-filler {p = Vᴰ Dᴰ.⋆ᴰ Mᴰ}
        (sym (Functor.F-seq (∫F F) (_ , V) (_ , M)))) i .fst .snd
    state-subst-filler {V = V} {M = M} Vᴰ Mᴰ i .snd =
      sym (Dᴰ.reind-revealed-filler {p = Vᴰ Dᴰ.⋆ᴰ Mᴰ}
        (sym (Functor.F-seq (∫F F) (_ , V) (_ , M)))) i .snd

    state-plug-filler : ∀
      {A : C.ob[ 𝒱 ]} {B B' : C.ob[ 𝒞 ]}
      {Aᴰ : Dᴰ.ob[ _ , F.F-obᴰ A ]} {Bᴰ : Dᴰ.ob[ _ , F.F-obᴰ B ]}
      {Bᴰ' : Dᴰ.ob[ _ , F.F-obᴰ B' ]}
      {M : C.Hom[ _ ][ A , B ]} {S : C.Hom[ _ ][ B , B' ]}
      (Mᴰ : Dᴰ.Hom[ _ , F.F-homᴰ M ][ Aᴰ , Bᴰ ])
      (Sᴰ : Dᴰ.Hom[ _ , F.F-homᴰ S ][ Bᴰ , Bᴰ' ])
      → Path
          (Σ[ N ∈ D.Hom[ _ ][ F.F-obᴰ A , F.F-obᴰ B' ] ]
            Dᴰ.Hom[ _ , N ][ Aᴰ , Bᴰ' ])
          (F.F-homᴰ (M C.⋆ᴰ S) , Mᴰ F*Cᴰ.⋆ᴰ Sᴰ)
          (F.F-homᴰ M D.⋆ᴰ F.F-homᴰ S , Mᴰ Dᴰ.⋆ᴰ Sᴰ)
    state-plug-filler {M = M} {S = S} Mᴰ Sᴰ i .fst =
      sym (Dᴰ.reind-revealed-filler {p = Mᴰ Dᴰ.⋆ᴰ Sᴰ}
        (sym (Functor.F-seq (∫F F) (_ , M) (_ , S)))) i .fst .snd
    state-plug-filler {M = M} {S = S} Mᴰ Sᴰ i .snd =
      sym (Dᴰ.reind-revealed-filler {p = Mᴰ Dᴰ.⋆ᴰ Sᴰ}
        (sym (Functor.F-seq (∫F F) (_ , M) (_ , S)))) i .snd

    -- Can this be simplified?
    module _
      {A₀ A₁ : C.ob[ 𝒱 ]} {B₀ B₁ : C.ob[ 𝒞 ]}
      {A₀ᴰ : Dᴰ.ob[ _ , F.F-obᴰ A₀ ]} {B₀ᴰ : Dᴰ.ob[ _ , F.F-obᴰ B₀ ]}
      {A₁ᴰ : Dᴰ.ob[ _ , F.F-obᴰ A₁ ]} {B₁ᴰ : Dᴰ.ob[ _ , F.F-obᴰ B₁ ]}
      {g : C.Hom[ _ ][ A₀ , B₀ ] → C.Hom[ _ ][ A₁ , B₁ ]}
      {ψ : Homo g (CState .fst A₀ B₀) (CState .fst A₁ B₁)}
      {g' : D.Hom[ _ ][ F.F-obᴰ A₀ , F.F-obᴰ B₀ ]
          → D.Hom[ _ ][ F.F-obᴰ A₁ , F.F-obᴰ B₁ ]}
      {ψ' : Homo g'
        (DState .fst (F.F-obᴰ A₀) (F.F-obᴰ B₀))
        (DState .fst (F.F-obᴰ A₁) (F.F-obᴰ B₁))}
      {gᴰ' : mapOver g'
        (λ M → Dᴰ.Hom[ _ , M ][ A₀ᴰ , B₀ᴰ ])
        (λ M → Dᴰ.Hom[ _ , M ][ A₁ᴰ , B₁ᴰ ])}
      (ψᴰ' : Homoᴰ gᴰ' ψ'
        (DᴰState .fst A₀ᴰ B₀ᴰ) (DᴰState .fst A₁ᴰ B₁ᴰ))
      {gᴰ : mapOver g
        (λ M → Dᴰ.Hom[ _ , F.F-homᴰ M ][ A₀ᴰ , B₀ᴰ ])
        (λ M → Dᴰ.Hom[ _ , F.F-homᴰ M ][ A₁ᴰ , B₁ᴰ ])}
      (gᴰ-filler : ∀ M Mᴰ → Path
        (Σ[ N ∈ D.Hom[ _ ][ F.F-obᴰ A₁ , F.F-obᴰ B₁ ] ]
          Dᴰ.Hom[ _ , N ][ A₁ᴰ , B₁ᴰ ])
        (F.F-homᴰ (g M) , gᴰ M Mᴰ)
        (g' (F.F-homᴰ M) , gᴰ' (F.F-homᴰ M) Mᴰ))
      where
      private
        module C₀ = StateAlg (CState .fst A₀ B₀)
        module D₁ᴰ where
          open StateAlgᴰ (DᴰState .fst A₁ᴰ B₁ᴰ) public
          open hSetReasoning
            (_ , isSetDHom)
            (λ M → Dᴰ.Hom[ _ , M ][ A₁ᴰ , B₁ᴰ ])
            using (rectifyOut) public
        module ψᴰ' = Homoᴰ ψᴰ'

        C₀ᴰ = StateAlgEffᴰReindex A₀ᴰ B₀ᴰ
        C₁ᴰ = StateAlgEffᴰReindex A₁ᴰ B₁ᴰ

        total-gᴰ' :
          (Σ[ M ∈ D.Hom[ _ ][ F.F-obᴰ A₀ , F.F-obᴰ B₀ ] ]
            Dᴰ.Hom[ _ , M ][ A₀ᴰ , B₀ᴰ ])
          → (Σ[ M ∈ D.Hom[ _ ][ F.F-obᴰ A₁ , F.F-obᴰ B₁ ] ]
            Dᴰ.Hom[ _ , M ][ A₁ᴰ , B₁ᴰ ])
        total-gᴰ' (M , Mᴰ) = g' M , gᴰ' M Mᴰ

      reindexHomoᴰ : Homoᴰ gᴰ ψ C₀ᴰ C₁ᴰ
      reindexHomoᴰ .Homoᴰ.rd-homᴰ Mt Mf Mtᴰ Mfᴰ
        rdtf rdtfᴰ p pᴰ = D₁ᴰ.rectifyOut $
        gᴰ-filler rdtf rdtfᴰ
        ∙ cong total-gᴰ' (ΣPathP (cong F.F-homᴰ p , pᴰ))
        ∙ cong total-gᴰ'
            (reindexStateAlgᴰ-rd-filler (FState A₀ B₀)
              (DᴰState .fst A₀ᴰ B₀ᴰ) isSetDHom Mtᴰ Mfᴰ)
        ∙ Homo.rd-hom' ψᴰ'.∫ (F.F-homᴰ Mt , Mtᴰ) (F.F-homᴰ Mf , Mfᴰ)
        ∙ cong₂ (D₁ᴰ.∫ .StateAlg.rd)
            (sym (gᴰ-filler Mt Mtᴰ)) (sym (gᴰ-filler Mf Mfᴰ))
        ∙ sym (reindexStateAlgᴰ-rd-filler (FState A₁ B₁)
            (DᴰState .fst A₁ᴰ B₁ᴰ) isSetDHom
            (gᴰ Mt Mtᴰ) (gᴰ Mf Mfᴰ))
      reindexHomoᴰ .Homoᴰ.wt-homᴰ b M Mᴰ
        wtbx wtbxᴰ p pᴰ = D₁ᴰ.rectifyOut $
        gᴰ-filler wtbx wtbxᴰ
        ∙ cong total-gᴰ' (ΣPathP (cong F.F-homᴰ p , pᴰ))
        ∙ cong total-gᴰ'
            (reindexStateAlgᴰ-wt-filler (FState A₀ B₀)
              (DᴰState .fst A₀ᴰ B₀ᴰ) isSetDHom b Mᴰ)
        ∙ Homo.wt-hom' ψᴰ'.∫ b (F.F-homᴰ M , Mᴰ)
        ∙ cong (D₁ᴰ.∫ .StateAlg.wt b) (sym (gᴰ-filler M Mᴰ))
        ∙ sym (reindexStateAlgᴰ-wt-filler (FState A₁ B₁)
            (DᴰState .fst A₁ᴰ B₁ᴰ) isSetDHom b (gᴰ M Mᴰ))

  StateAlgEnrichmentᴰReindex : StateAlgEnrichmentᴰ CState F*Cᴰ
  StateAlgEnrichmentᴰReindex .fst = StateAlgEffᴰReindex
  StateAlgEnrichmentᴰReindex .snd .fst {A} {A'} {B} {V = V} Vᴰ =
    reindexHomoᴰ
      (DᴰState .snd .fst Vᴰ)
      (λ _ Mᴰ → state-subst-filler Vᴰ Mᴰ)
  StateAlgEnrichmentᴰReindex .snd .snd {A} {B} {B'} {S = S} Sᴰ =
    reindexHomoᴰ
      (DᴰState .snd .snd Sᴰ)
      (λ _ Mᴰ → state-plug-filler Mᴰ Sᴰ)
