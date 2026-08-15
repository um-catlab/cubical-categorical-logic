module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.GetSetCurrent where

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Discrete
open import Cubical.Data.Fin
open import Cubical.Data.Bool hiding (_≤_ ; isProp≤)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-refl ; isProp≤)
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt

open Functor
open NatTrans
open PshHom

{- Reading a location and writing its current value has no effect.

  get i (λ b → set i b t) = t
-}
get-set-currentᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (t : Γ ⊢ T .F-ob A) →
  getᵗ i (setᵗ (V.π₁ V.⋆ i) V.π₂ (V.π₁ V.⋆ t)) ≡ t
get-set-currentᵗ {Γ = Γ} {A = A} i t =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext {A = A} λ m n≤m σ →
    let
      iₙ = i .N-ob n γ
      γₘ = Γ .F-hom n≤m γ
      iₘ = i .N-ob m γₘ
      wi = weakenRef n≤m iₙ
      i-nat = funExt⁻ (i .N-hom n≤m) γ
      write≡wi = funExt⁻ (Ref .F-id) iₘ ∙ i-nat
      store-path =
        cong (λ r → updateStore {n = m} r
          (lookupStore {n = m} wi σ) σ) write≡wi
        ∙ update-current {n = m} wi σ
    in
    getᵗ-run i (setᵗ (V.π₁ V.⋆ i) V.π₂ (V.π₁ V.⋆ t))
      n γ m n≤m σ
    ∙ setᵗ-run (V.π₁ V.⋆ i) V.π₂ (V.π₁ V.⋆ t)
        m (γₘ , lookupStore {n = m} wi σ) m ≤-refl σ
    ∙ cong (λ τ → t .N-ob m γₘ m ≤-refl τ) store-path
    ∙ cong (λ u → u m ≤-refl σ)
        (funExt⁻ (t .N-hom n≤m) γ)
    ∙ cong (λ q → t .N-ob n γ m q σ) (isProp≤ _ _))
