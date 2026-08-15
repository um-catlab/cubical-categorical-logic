module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.GetGetCommute where

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Discrete
open import Cubical.Data.Bool hiding (_≤_ ; isProp≤)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-refl ; isProp≤)
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt

open Functor
open NatTrans
open PshHom

{- Reads commute.  No distinctness assumption is required.

  get i (λ b → get j (λ c → k b c))
    = get j (λ c → get i (λ b → k b c))
-}
get-get-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref)
  (k : (Γ V.× BoolVal) V.× BoolVal ⊢ T .F-ob A) →
  getᵗ i (getᵗ (V.π₁ V.⋆ j) k) ≡
  getᵗ j (getᵗ (V.π₁ V.⋆ i) (swapLast V.⋆ k))
get-get-commuteᵗ {Γ = Γ} {A = A} i j k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext {A = A} λ m n≤m σ →
    let
      γₘ = Γ .F-hom n≤m γ
      wi = weakenRef n≤m (i .N-ob n γ)
      wj = weakenRef n≤m (j .N-ob n γ)
      vi = lookupStore {n = m} wi σ
      vj = lookupStore {n = m} wj σ
      iₘ = i .N-ob m γₘ
      jₘ = j .N-ob m γₘ
      ri = weakenRef ≤-refl iₘ
      rj = weakenRef ≤-refl jₘ
      context-i-id = funExt⁻ ((Γ V.× BoolVal) .F-id) (γₘ , vi)
      γ-id = funExt⁻ (Γ .F-id) γₘ
      ri≡wi = funExt⁻ (Ref .F-id) iₘ ∙ funExt⁻ (i .N-hom n≤m) γ
      rj≡wj = funExt⁻ (Ref .F-id) jₘ ∙ funExt⁻ (j .N-hom n≤m) γ
    in
    getᵗ-run i (getᵗ (V.π₁ V.⋆ j) k) n γ m n≤m σ
    ∙ getᵗ-run (V.π₁ V.⋆ j) k m (γₘ , vi) m ≤-refl σ
    ∙ cong (λ δ → k .N-ob m
        (δ , lookupStore {n = m} rj σ) m ≤-refl σ) context-i-id
    ∙ cong (λ c → k .N-ob m ((γₘ , vi) , c) m ≤-refl σ)
        (cong σ rj≡wj)
    ∙ sym (cong (λ b → k .N-ob m ((γₘ , b) , vj) m ≤-refl σ)
        (cong σ ri≡wi))
    ∙ sym (cong (λ δ → k .N-ob m
        ((δ , lookupStore {n = m} ri σ) , vj) m ≤-refl σ) γ-id)
    ∙ sym (getᵗ-run (V.π₁ V.⋆ i) (swapLast V.⋆ k)
        m (γₘ , vj) m ≤-refl σ)
    ∙ sym (getᵗ-run j (getᵗ (V.π₁ V.⋆ i) (swapLast V.⋆ k))
        n γ m n≤m σ))
