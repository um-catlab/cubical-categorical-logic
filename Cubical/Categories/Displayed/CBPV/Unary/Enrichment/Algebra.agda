{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Algebra where

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
open import Cubical.Algebra.Signature.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓO ℓA : Level

open Category hiding (_∘_)
open Categoryᴰ
open Functor

module _ (C : CBPVCat ℓ ℓ') (Sig : Signature ℓO ℓA) where
  open Signature Sig
  private module C = Fibers C

  AlgebraEnrichment : Type _
  AlgebraEnrichment =
    Σ[ AlgebraEff ∈ (∀ (A : C.ob[ 𝒱 ]) (B : C.ob[ 𝒞 ])
      → AlgebraWithCarrier (C.Hom[ _ ][ A , B ])) ]
    (∀ {A A'} (V : C.Hom[ _ ][ A , A' ]) B
      → isHomoSimpl (_ , AlgebraEff A' B) (_ , AlgebraEff A B)
          (λ M → V C.⋆ᴰ M))
    ×
    (∀ {B B'} (S : C.Hom[ _ ][ B , B' ]) A
      → isHomoSimpl (_ , AlgebraEff A B) (_ , AlgebraEff A B')
          (λ M → M C.⋆ᴰ S))

module _ {C : CBPVCat ℓ ℓ'} (Sig : Signature ℓO ℓA)
  (CAlg : AlgebraEnrichment C Sig)
  (Cᴰ : CBPVCatᴰ C ℓᴰ ℓᴰ') where
  open Signature Sig
  private module C = Fibers C
  private module Cᴰ = Fibers Cᴰ

  AlgebraEnrichmentᴰ : Type _
  AlgebraEnrichmentᴰ =
    Σ[ AlgebraEffᴰ ∈ (∀ {A B}
      (Aᴰ : Cᴰ.ob[ _ , A ]) (Bᴰ : Cᴰ.ob[ _ , B ])
      → AlgebraᴰWithCarrier (_ , CAlg .fst A B)
          (λ M → Cᴰ.Hom[ _ , M ][ Aᴰ , Bᴰ ])) ]
    (∀ {A A' B}
      {Aᴰ : Cᴰ.ob[ _ , A ]} {Aᴰ' : Cᴰ.ob[ _ , A' ]}
      {Bᴰ : Cᴰ.ob[ _ , B ]} {V : _}
      (Vᴰ : Cᴰ.Hom[ _ , V ][ Aᴰ , Aᴰ' ])
      → isHomoᴰSimpl
          ((λ M → V C.⋆ᴰ M) , CAlg .snd .fst V B)
          (_ , AlgebraEffᴰ Aᴰ' Bᴰ) (_ , AlgebraEffᴰ Aᴰ Bᴰ)
          (λ _ Mᴰ → Vᴰ Cᴰ.⋆ᴰ Mᴰ))
    ×
    (∀ {A B B'}
      {Aᴰ : Cᴰ.ob[ _ , A ]} {Bᴰ : Cᴰ.ob[ _ , B ]}
      {Bᴰ' : Cᴰ.ob[ _ , B' ]} {S : _}
      (Sᴰ : Cᴰ.Hom[ _ , S ][ Bᴰ , Bᴰ' ])
      → isHomoᴰSimpl
          ((λ M → M C.⋆ᴰ S) , CAlg .snd .snd S A)
          (_ , AlgebraEffᴰ Aᴰ Bᴰ) (_ , AlgebraEffᴰ Aᴰ Bᴰ')
          (λ _ Mᴰ → Mᴰ Cᴰ.⋆ᴰ Sᴰ))

module _ {C : CBPVCat ℓ ℓ'} {D : CBPVCat ℓD ℓD'}
  (Sig : Signature ℓO ℓA)
  (F : Functorⱽ C D)
  (CAlg : AlgebraEnrichment C Sig) (DAlg : AlgebraEnrichment D Sig)
  where
  open Signature Sig

  PreservesAlgebraEnrichment : Type _
  PreservesAlgebraEnrichment = ∀ A B →
    isHomoSimpl (_ , CAlg .fst A B)
      (_ , DAlg .fst (F .Functorᴰ.F-obᴰ A) (F .Functorᴰ.F-obᴰ B))
      (F .Functorᴰ.F-homᴰ)

module _ {ℓO ℓA} (Sig : Signature ℓO ℓA) where
  open Signature Sig

  reindexAlgebraᴰ-op-filler :
    {A : Algebra ℓ} {B : Algebra ℓ'}
    (ϕ : Homo A B) (Bᴰ : Algebraᴰ B ℓᴰ)
    (op : Op) (γ : Arity op → A .fst)
    (γᴰ : ∀ v → Bᴰ .fst (ϕ .fst (γ v)))
    (op⟨γ⟩ : A .fst) (op∘γ≡op⟨γ⟩ : A .snd op γ ≡ op⟨γ⟩)
    → Path (∫Algebra Bᴰ .fst)
        (ϕ .fst op⟨γ⟩ ,
          (ϕ * Bᴰ) .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩)
        (B .snd op (ϕ .fst ∘ γ) ,
          Bᴰ .snd op (ϕ .fst ∘ γ) γᴰ
            (B .snd op (ϕ .fst ∘ γ)) refl)
  reindexAlgebraᴰ-op-filler ϕ Bᴰ op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ i .fst =
    ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ (~ i)
  reindexAlgebraᴰ-op-filler {B = B} ϕ Bᴰ op γ γᴰ
    op⟨γ⟩ op∘γ≡op⟨γ⟩ i .snd =
    Bᴰ .snd op (ϕ .fst ∘ γ) γᴰ
      (ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ (~ i))
      (λ j → ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ (j ∧ ~ i))

  totalHomoᴰ :
    {A : Algebra ℓ} {B : Algebra ℓ'}
    {Aᴰ : Algebraᴰ A ℓᴰ} {Bᴰ : Algebraᴰ B ℓᴰ'}
    {ϕ : Homo A B}
    → Homoᴰ ϕ Aᴰ Bᴰ → Homo (∫Algebra Aᴰ) (∫Algebra Bᴰ)
  totalHomoᴰ {A = A} {B = B} {Aᴰ = Aᴰ} {Bᴰ = Bᴰ} {ϕ = ϕ} ϕᴰ =
    ∫intro (_⋆H_ {C = B} (Signature.Fst Sig) ϕ) section
    where
    section : Section (_⋆H_ {C = B} (Signature.Fst Sig) ϕ * Bᴰ)
    section .fst z = ϕᴰ .fst (z .fst) (z .snd)
    section .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      ϕᴰ .snd op (fst ∘ γ) (snd ∘ γ)
        (op⟨γ⟩ .fst) (cong fst op∘γ≡op⟨γ⟩)
        (op⟨γ⟩ .snd)
        (Signature.Snd Sig {Aᴰ = Aᴰ} .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)

module _
  {C : CBPVCat ℓ ℓ'} {D : CBPVCat ℓD ℓD'}
  (Sig : Signature ℓO ℓA)
  (F : Functorⱽ C D)
  (CAlg : AlgebraEnrichment C Sig) (DAlg : AlgebraEnrichment D Sig)
  (FAlg : PreservesAlgebraEnrichment Sig F CAlg DAlg)
  (Dᴰ : CBPVCatᴰ D ℓCᴰ ℓCᴰ')
  (DᴰAlg : AlgebraEnrichmentᴰ Sig DAlg Dᴰ)
  where
  open Signature Sig
  private
    module C = Fibers C
    module D = Fibers D
    module Dᴰ = Fibers Dᴰ
    module F = Functorᴰ F

    FAlgHomo : ∀ A B → Homo (_ , CAlg .fst A B)
      (_ , DAlg .fst (F.F-obᴰ A) (F.F-obᴰ B))
    FAlgHomo A B = F.F-homᴰ , FAlg A B

    F*Cᴰ = reindex Dᴰ (∫F F)
    module F*Cᴰ = Fibers F*Cᴰ

    AlgebraEffᴰReindex : ∀ {A : C.ob[ 𝒱 ]} {B : C.ob[ 𝒞 ]}
      (Aᴰ : Dᴰ.ob[ _ , F.F-obᴰ A ]) (Bᴰ : Dᴰ.ob[ _ , F.F-obᴰ B ])
      → Algebraᴰ (_ , CAlg .fst A B) ℓCᴰ'
    AlgebraEffᴰReindex {A} {B} Aᴰ Bᴰ .fst M =
      Dᴰ.Hom[ _ , F.F-homᴰ M ][ Aᴰ , Bᴰ ]
    AlgebraEffᴰReindex {A} {B} Aᴰ Bᴰ .snd
      op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
        DᴰAlg .fst Aᴰ Bᴰ op (F.F-homᴰ ∘ γ) γᴰ
          (F.F-homᴰ op⟨γ⟩)
          (FAlg A B op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)

    algebra-subst-filler : ∀
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
    algebra-subst-filler {V = V} {M = M} Vᴰ Mᴰ i .fst =
      sym (Dᴰ.reind-revealed-filler {p = Vᴰ Dᴰ.⋆ᴰ Mᴰ}
        (sym (Functor.F-seq (∫F F) (_ , V) (_ , M)))) i .fst .snd
    algebra-subst-filler {V = V} {M = M} Vᴰ Mᴰ i .snd =
      sym (Dᴰ.reind-revealed-filler {p = Vᴰ Dᴰ.⋆ᴰ Mᴰ}
        (sym (Functor.F-seq (∫F F) (_ , V) (_ , M)))) i .snd

    algebra-plug-filler : ∀
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
    algebra-plug-filler {M = M} {S = S} Mᴰ Sᴰ i .fst =
      sym (Dᴰ.reind-revealed-filler {p = Mᴰ Dᴰ.⋆ᴰ Sᴰ}
        (sym (Functor.F-seq (∫F F) (_ , M) (_ , S)))) i .fst .snd
    algebra-plug-filler {M = M} {S = S} Mᴰ Sᴰ i .snd =
      sym (Dᴰ.reind-revealed-filler {p = Mᴰ Dᴰ.⋆ᴰ Sᴰ}
        (sym (Functor.F-seq (∫F F) (_ , M) (_ , S)))) i .snd

    module _
      {A₀ A₁ : C.ob[ 𝒱 ]} {B₀ B₁ : C.ob[ 𝒞 ]}
      {A₀ᴰ : Dᴰ.ob[ _ , F.F-obᴰ A₀ ]} {B₀ᴰ : Dᴰ.ob[ _ , F.F-obᴰ B₀ ]}
      {A₁ᴰ : Dᴰ.ob[ _ , F.F-obᴰ A₁ ]} {B₁ᴰ : Dᴰ.ob[ _ , F.F-obᴰ B₁ ]}
      {ψ : Homo (_ , CAlg .fst A₀ B₀) (_ , CAlg .fst A₁ B₁)}
      {ψ' : Homo
        (_ , DAlg .fst (F.F-obᴰ A₀) (F.F-obᴰ B₀))
        (_ , DAlg .fst (F.F-obᴰ A₁) (F.F-obᴰ B₁))}
      (ψᴰ' : Homoᴰ ψ'
        (_ , DᴰAlg .fst A₀ᴰ B₀ᴰ) (_ , DᴰAlg .fst A₁ᴰ B₁ᴰ))
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
          (_ , DAlg .fst (F.F-obᴰ A₀) (F.F-obᴰ B₀)) ℓCᴰ'
        D₀ᴰ .fst M = Dᴰ.Hom[ _ , M ][ A₀ᴰ , B₀ᴰ ]
        D₀ᴰ .snd = DᴰAlg .fst A₀ᴰ B₀ᴰ

        D₁ᴰ : Algebraᴰ
          (_ , DAlg .fst (F.F-obᴰ A₁) (F.F-obᴰ B₁)) ℓCᴰ'
        D₁ᴰ .fst M = Dᴰ.Hom[ _ , M ][ A₁ᴰ , B₁ᴰ ]
        D₁ᴰ .snd = DᴰAlg .fst A₁ᴰ B₁ᴰ

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
              (reindexAlgebraᴰ-op-filler Sig (FAlgHomo A₀ B₀) D₀ᴰ
                op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩)
          ∙ sym (totalHomoᴰ Sig ψᴰ' .snd op
              (λ v → F.F-homᴰ (γ v) , γᴰ v) _ refl)
          ∙ cong (∫Algebra D₁ᴰ .snd op)
              (funExt λ v → sym (gᴰ-filler (γ v) (γᴰ v)))
          ∙ sym (reindexAlgebraᴰ-op-filler Sig (FAlgHomo A₁ B₁) D₁ᴰ op
              (ψ .fst ∘ γ) (λ v → gᴰ (γ v) (γᴰ v))
              (ψ .fst op⟨γ⟩)
              (ψ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩))

  AlgebraEnrichmentᴰReindex : AlgebraEnrichmentᴰ Sig CAlg F*Cᴰ
  AlgebraEnrichmentᴰReindex .fst Aᴰ Bᴰ =
    AlgebraEffᴰReindex Aᴰ Bᴰ .snd
  AlgebraEnrichmentᴰReindex .snd .fst
    {A} {A'} {B} {V = V} Vᴰ =
      reindexHomoᴰ
        {ψ = (λ M → V C.⋆ᴰ M) , CAlg .snd .fst V B}
        {ψ' = (λ M → F.F-homᴰ V D.⋆ᴰ M) ,
          DAlg .snd .fst (F.F-homᴰ V) (F.F-obᴰ B)}
        ((λ _ Mᴰ → Vᴰ Dᴰ.⋆ᴰ Mᴰ) , DᴰAlg .snd .fst Vᴰ)
        (λ _ Mᴰ → algebra-subst-filler Vᴰ Mᴰ) .snd
  AlgebraEnrichmentᴰReindex .snd .snd
    {A} {B} {B'} {S = S} Sᴰ =
      reindexHomoᴰ
        {ψ = (λ M → M C.⋆ᴰ S) , CAlg .snd .snd S A}
        {ψ' = (λ M → M D.⋆ᴰ F.F-homᴰ S) ,
          DAlg .snd .snd (F.F-homᴰ S) (F.F-obᴰ A)}
        ((λ _ Mᴰ → Mᴰ Dᴰ.⋆ᴰ Sᴰ) , DᴰAlg .snd .snd Sᴰ)
        (λ _ Mᴰ → algebra-plug-filler Mᴰ Sᴰ) .snd
