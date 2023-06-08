module Syntax.STLC.Semantics.CTStructure.Soundness where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Data.Unit
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors

open import NamedContext
open import UMP
open import NaturalModels.CTStructure
open import Syntax.STLC renaming (Ty to STy)
open import Syntax.STLC.Semantics.CTStructure.Interpretation
open import Syntax.STLC.Semantics.CTStructure.Lindenbaum
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable

private
  variable
    ℓ ℓ' ℓb ℓb' ℓc ℓc' ℓt ℓt' : Level
module _ {Σ₀ : Sig₀ ℓ}{Σ₁ : Sig₁ Σ₀ ℓ'}
         (S : CTStructure ℓb ℓb' ℓt)
         (i₀ : Interp₀ Σ₀ S)
         (i₁ : Interp₁ {S = S} i₀ Σ₁)
         where
  open Category
  open Functor
  open CT-Functor
  open CartesianFunctor
  open UnivElt
  open isUniversal
  open Ctx
  open Sig₁

  open CTStructure(S)
  open CartesianCategory(B)

  private
    Term = Tm {Σ₀ = Σ₀} Σ₁
    Subst = STT-subst Σ₁

  ctx-sem : Ctx (STy Σ₀) → cat .ob
  ctx-sem = interpCtx {Σ₀ = Σ₀} {S = S} i₀

  mutual
    term-sem : ∀ {Γ A} → Term Γ A → cat [ ctx-sem Γ , sole (i₀ A) ]
    subst-sem : ∀ {Δ Γ} → Subst Δ Γ → cat [ ctx-sem Δ , ctx-sem Γ ]

    term-sem (ivar x) = π _ _ x
    term-sem (fun-app f γ) = i₁ f ∘⟨ cat ⟩ subst-sem γ

    subst-sem {Δ = Δ}{Γ = Γ} γ =
      prod-I (varFinSet Γ)
             (λ x → sole (i₀ (Γ .el x)))
             λ x → term-sem (γ x)

  mutual
    term-sem-comp : ∀ {Δ Γ A} → (M : Term Γ A) → (γ : Subst Δ Γ)
                  → term-sem (M ⟨ γ ⟩) ≡ term-sem M ∘⟨ cat ⟩ subst-sem γ
    subst-sem-comp : ∀ {Ξ Δ Γ} → (γ : Subst Δ Γ) (δ : Subst Ξ Δ)
                   → subst-sem {Γ = Γ} (comp-subst {Γ = Γ} γ δ) ≡
                     (subst-sem γ ∘⟨ cat ⟩ subst-sem δ)

    term-sem-comp {Δ} {Γ} {.(Γ .el x)} (ivar x) γ = sym (π∘prod-I _ _ _ _)
    term-sem-comp {Δ} {Γ} {.(Σ₁ .tgt f)} (fun-app f δ) γ =
      i₁ f ∘⟨ cat ⟩ subst-sem (comp-subst {Γ = Σ₁ .src f} δ γ)
        ≡[ i ]⟨ i₁ f ∘⟨ cat ⟩ subst-sem-comp δ γ i ⟩
      i₁ f ∘⟨ cat ⟩ (subst-sem δ ∘⟨ cat ⟩ subst-sem γ)
        ≡⟨ cat .⋆Assoc _ _ _ ⟩
      (i₁ f ∘⟨ cat ⟩ subst-sem δ) ∘⟨ cat ⟩ subst-sem γ ∎
    subst-sem-comp {Ξ} {Δ} {Γ} γ δ =
      subst-sem {Γ = Γ} (comp-subst {Γ = Γ} γ δ)
        ≡[ i ]⟨ prod-I _ _ (λ x → term-sem-comp (γ x) δ i) ⟩
      prod-I (varFinSet Γ) (λ x → sole (i₀ (Γ .el x)))
        (λ x → term-sem (γ x) ∘⟨ cat ⟩ subst-sem δ)
        ≡⟨ sym (coinduction-natural (finite-products _ _ .universal) _ _) ⟩
      subst-sem γ ∘⟨ cat ⟩ subst-sem δ
      ∎

  soundness : CT-Functor (Lindenbaum {Σ₀ = Σ₀}{Σ₁ = Σ₁}) S
  soundness .F-B .func .F-ob = ctx-sem
  soundness .F-B .func .F-hom = subst-sem
  soundness .F-B .func .F-id {x = Γ} =
    prod-I⟨π⟩ (varFinSet Γ) (λ x → sole (i₀ (Γ .el x)))
  soundness .F-B .func .F-seq δ γ = subst-sem-comp γ δ
  soundness .F-B .preserves-fin-products J D =
    nestProd cat (J .fst) (λ j → D j .var) (λ j x → sole (i₀ (D j .el x)))
                 (λ j → finite-products _ _)
                 (finite-products _ _)
  soundness .F-Ty = i₀
  soundness .F-agree {A} =
    sameUMP→CatIso cat (Πᴾ cat Unit (λ tt → cat [-, sole (i₀ A) ]))
      (record {
        vertex = _ ;
        element = _ ;
        universal = unaryProd _ (sole (i₀ A))
      })
      (finite-products (_ , isFinSetUnit) (λ tt → sole (i₀ A)))
