-- Enrichment of a CBPV Model in Models of a Theory: a way to add
-- algebraic effects to a CBPV model. The computations carry an
-- algebra structure and substitution and plugging are homomorphisms.

{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Model where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.More

open import Cubical.Data.Sigma

open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝒱; r to 𝒞; ≤Vertex to ≤Kind)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.Instances.Algebra.Model
open import Cubical.Categories.Displayed.Instances.Reindex

open import Cubical.Algebra.Theory.Base

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
    C.Hom[ _ ][ A , B ] , Categoryᴰ.isSetHomᴰ C
  ModelEnrichmentModel CModel A B .snd = CModel .fst A B

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

    F*Cᴰ = reindex Dᴰ (∫F F)
    module F*Cᴰ = Fibers F*Cᴰ

    FModelHomo : ∀ A B → Homo
      (Model→Algebra (ModelEnrichmentModel C T CModel A B))
      (Model→Algebra
        (ModelEnrichmentModel D T DModel (F.F-obᴰ A) (F.F-obᴰ B)))
    FModelHomo A B .fst = F.F-homᴰ
    FModelHomo A B .snd = FModel A B

    DᴰModelAt : ∀ {A : D.ob[ 𝒱 ]} {B : D.ob[ 𝒞 ]}
      (Aᴰ : Dᴰ.ob[ _ , A ]) (Bᴰ : Dᴰ.ob[ _ , B ])
      → Modelᴰ (ModelEnrichmentModel D T DModel A B) ℓCᴰ'
    DᴰModelAt Aᴰ Bᴰ .fst M =
      Dᴰ.Hom[ _ , M ][ Aᴰ , Bᴰ ] , Categoryᴰ.isSetHomᴰ Dᴰ
    DᴰModelAt Aᴰ Bᴰ .snd = DᴰModel .fst Aᴰ Bᴰ

    PulledModel : ∀ {A : C.ob[ 𝒱 ]} {B : C.ob[ 𝒞 ]}
      (Aᴰ : Dᴰ.ob[ _ , F.F-obᴰ A ]) (Bᴰ : Dᴰ.ob[ _ , F.F-obᴰ B ])
      → Modelᴰ (ModelEnrichmentModel C T CModel A B) ℓCᴰ'
    PulledModel {A} {B} Aᴰ Bᴰ =
      Theory._*_ T (FModelHomo A B) (DᴰModelAt Aᴰ Bᴰ)

    ModelEffᴰReindex : ∀ {A : C.ob[ 𝒱 ]} {B : C.ob[ 𝒞 ]}
      (Aᴰ : Dᴰ.ob[ _ , F.F-obᴰ A ]) (Bᴰ : Dᴰ.ob[ _ , F.F-obᴰ B ])
      → ModelᴰWithCarrier (ModelEnrichmentModel C T CModel A B)
          (λ M → F*Cᴰ.Hom[ _ , M ][ Aᴰ , Bᴰ ])
    ModelEffᴰReindex Aᴰ Bᴰ = PulledModel Aᴰ Bᴰ .snd

    AlgebraEffᴰReindex : ∀ {A : C.ob[ 𝒱 ]} {B : C.ob[ 𝒞 ]}
      (Aᴰ : Dᴰ.ob[ _ , F.F-obᴰ A ]) (Bᴰ : Dᴰ.ob[ _ , F.F-obᴰ B ])
      → Algebraᴰ (_ , CModel .fst A B .fst) ℓCᴰ'
    AlgebraEffᴰReindex {A} {B} Aᴰ Bᴰ .fst M =
      Dᴰ.Hom[ _ , F.F-homᴰ M ][ Aᴰ , Bᴰ ]
    AlgebraEffᴰReindex {A} {B} Aᴰ Bᴰ .snd
      op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
        DᴰModel .fst Aᴰ Bᴰ .fst op (F.F-homᴰ ∘ γ) γᴰ
          (F.F-homᴰ op⟨γ⟩)
          (FModel A B op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)

    reindex-subst-filler : ∀
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
    reindex-subst-filler {V = V} {M = M} Vᴰ Mᴰ i .fst =
      sym (Dᴰ.reind-revealed-filler {p = Vᴰ Dᴰ.⋆ᴰ Mᴰ}
        (sym (Functor.F-seq (∫F F) (_ , V) (_ , M)))) i .fst .snd
    reindex-subst-filler {V = V} {M = M} Vᴰ Mᴰ i .snd =
      sym (Dᴰ.reind-revealed-filler {p = Vᴰ Dᴰ.⋆ᴰ Mᴰ}
        (sym (Functor.F-seq (∫F F) (_ , V) (_ , M)))) i .snd

    reindex-plug-filler : ∀
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
    reindex-plug-filler {M = M} {S = S} Mᴰ Sᴰ i .fst =
      sym (Dᴰ.reind-revealed-filler {p = Mᴰ Dᴰ.⋆ᴰ Sᴰ}
        (sym (Functor.F-seq (∫F F) (_ , M) (_ , S)))) i .fst .snd
    reindex-plug-filler {M = M} {S = S} Mᴰ Sᴰ i .snd =
      sym (Dᴰ.reind-revealed-filler {p = Mᴰ Dᴰ.⋆ᴰ Sᴰ}
        (sym (Functor.F-seq (∫F F) (_ , M) (_ , S)))) i .snd

    module _
      {A₀ A₁ : C.ob[ 𝒱 ]} {B₀ B₁ : C.ob[ 𝒞 ]}
      {A₀ᴰ : Dᴰ.ob[ _ , F.F-obᴰ A₀ ]} {B₀ᴰ : Dᴰ.ob[ _ , F.F-obᴰ B₀ ]}
      {A₁ᴰ : Dᴰ.ob[ _ , F.F-obᴰ A₁ ]} {B₁ᴰ : Dᴰ.ob[ _ , F.F-obᴰ B₁ ]}
      {ψ : Homo (_ , CModel .fst A₀ B₀ .fst) (_ , CModel .fst A₁ B₁ .fst)}
      {ψ' : Homo
        (_ , DModel .fst (F.F-obᴰ A₀) (F.F-obᴰ B₀) .fst)
        (_ , DModel .fst (F.F-obᴰ A₁) (F.F-obᴰ B₁) .fst)}
      (ψᴰ' : Homoᴰ ψ'
        (_ , DᴰModel .fst A₀ᴰ B₀ᴰ .fst) (_ , DᴰModel .fst A₁ᴰ B₁ᴰ .fst))
      {gᴰ : mapOver (ψ .fst)
        (λ M → Dᴰ.Hom[ _ , F.F-homᴰ M ][ A₀ᴰ , B₀ᴰ ])
        (λ M → Dᴰ.Hom[ _ , F.F-homᴰ M ][ A₁ᴰ , B₁ᴰ ])}
      (gᴰ-filler : ∀ M Mᴰ → Path
        (Σ[ N ∈ D.Hom[ _ ][ F.F-obᴰ A₁ , F.F-obᴰ B₁ ] ]
          Dᴰ.Hom[ _ , N ][ A₁ᴰ , B₁ᴰ ])
        (F.F-homᴰ (ψ .fst M) , gᴰ M Mᴰ)
        (ψ' .fst (F.F-homᴰ M) , ψᴰ' .fst (F.F-homᴰ M) Mᴰ))
      where
      private
        C₀ᴰ = AlgebraEffᴰReindex A₀ᴰ B₀ᴰ
        C₁ᴰ = AlgebraEffᴰReindex A₁ᴰ B₁ᴰ

        D₀ᴰ : Algebraᴰ
          (_ , DModel .fst (F.F-obᴰ A₀) (F.F-obᴰ B₀) .fst) ℓCᴰ'
        D₀ᴰ .fst M = Dᴰ.Hom[ _ , M ][ A₀ᴰ , B₀ᴰ ]
        D₀ᴰ .snd = DᴰModel .fst A₀ᴰ B₀ᴰ .fst

        D₁ᴰ : Algebraᴰ
          (_ , DModel .fst (F.F-obᴰ A₁) (F.F-obᴰ B₁) .fst) ℓCᴰ'
        D₁ᴰ .fst M = Dᴰ.Hom[ _ , M ][ A₁ᴰ , B₁ᴰ ]
        D₁ᴰ .snd = DᴰModel .fst A₁ᴰ B₁ᴰ .fst

        module D₁ᴰReasoning where
          open hSetReasoning
            (_ , Categoryᴰ.isSetHomᴰ D)
            (λ M → Dᴰ.Hom[ _ , M ][ A₁ᴰ , B₁ᴰ ])
            using (rectifyOut) public

        total-gᴰ' :
          (Σ[ M ∈ D.Hom[ _ ][ F.F-obᴰ A₀ , F.F-obᴰ B₀ ] ]
            Dᴰ.Hom[ _ , M ][ A₀ᴰ , B₀ᴰ ])
          → (Σ[ M ∈ D.Hom[ _ ][ F.F-obᴰ A₁ , F.F-obᴰ B₁ ] ]
            Dᴰ.Hom[ _ , M ][ A₁ᴰ , B₁ᴰ ])
        total-gᴰ' (M , Mᴰ) = ψ' .fst M , ψᴰ' .fst M Mᴰ

      reindexHomoᴰ : Homoᴰ ψ C₀ᴰ C₁ᴰ
      reindexHomoᴰ .fst = gᴰ
      reindexHomoᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
        op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ = D₁ᴰReasoning.rectifyOut $ sym $
          gᴰ-filler op⟨γ⟩ op⟨γᴰ⟩
          ∙ cong total-gᴰ'
              (ΣPathP (refl , sym op∘γᴰ≡op⟨γᴰ⟩))
          ∙ cong total-gᴰ'
              (reindexAlgebraᴰ-op-filler (FModelHomo A₀ B₀) D₀ᴰ
                op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩)
          ∙ sym (totalHomoᴰ ψᴰ' .snd op
              (λ v → F.F-homᴰ (γ v) , γᴰ v) _ refl)
          ∙ cong (∫Algebra D₁ᴰ .snd op)
              (funExt λ v → sym (gᴰ-filler (γ v) (γᴰ v)))
          ∙ sym (reindexAlgebraᴰ-op-filler (FModelHomo A₁ B₁) D₁ᴰ op
              (ψ .fst ∘ γ) (λ v → gᴰ (γ v) (γᴰ v))
              (ψ .fst op⟨γ⟩)
              (ψ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩))

  ModelEnrichmentᴰReindex : ModelEnrichmentᴰ T CModel F*Cᴰ
  ModelEnrichmentᴰReindex .fst = ModelEffᴰReindex
  ModelEnrichmentᴰReindex .snd .fst
    {A} {A'} {B} {V = V} Vᴰ =
      reindexHomoᴰ
        {ψ = (λ M → V C.⋆ᴰ M) , CModel .snd .fst V B}
        {ψ' = (λ M → F.F-homᴰ V D.⋆ᴰ M) ,
          DModel .snd .fst (F.F-homᴰ V) (F.F-obᴰ B)}
        ((λ _ Mᴰ → Vᴰ Dᴰ.⋆ᴰ Mᴰ) , DᴰModel .snd .fst Vᴰ)
        (λ _ Mᴰ → reindex-subst-filler Vᴰ Mᴰ) .snd
  ModelEnrichmentᴰReindex .snd .snd
    {A} {B} {B'} {S = S} Sᴰ =
      reindexHomoᴰ
        {ψ = (λ M → M C.⋆ᴰ S) , CModel .snd .snd S A}
        {ψ' = (λ M → M D.⋆ᴰ F.F-homᴰ S) ,
          DModel .snd .snd (F.F-homᴰ S) (F.F-obᴰ A)}
        ((λ _ Mᴰ → Mᴰ Dᴰ.⋆ᴰ Sᴰ) , DᴰModel .snd .snd Sᴰ)
        (λ _ Mᴰ → reindex-plug-filler Mᴰ Sᴰ) .snd
