module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.SetGetSame where

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

{- Reading immediately after writing returns the written value.

  set i b (get i k) = set i b (k b)
-}
set-get-sameᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (b : Γ ⊢ BoolVal)
  (k : Γ V.× BoolVal ⊢ T .F-ob A) →
  setᵗ i b (getᵗ i k) ≡ setᵗ i b ((V.id V.,p b) V.⋆ k)
set-get-sameᵗ {Γ = Γ} {A = A} i b k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext {A = A} λ m n≤m σ →
    let
      r = weakenRef n≤m (i .N-ob n γ)
      v = b .N-ob n γ
      σ' = updateStore {n = m} r v σ
    in
    setᵗ-run i b (getᵗ i k) n γ m n≤m σ
    ∙ getᵗ-run i k n γ m n≤m σ'
    ∙ cong (λ c → k .N-ob m (Γ .F-hom n≤m γ , c)
        m ≤-refl σ')
        (lookup-update-same {n = m} r v σ)
    ∙ cong (λ u → u m ≤-refl σ')
        (funExt⁻ (k .N-hom n≤m) (γ , v))
    ∙ cong (λ q → k .N-ob n (γ , v) m q σ') (isProp≤ _ _)
    ∙ sym (setᵗ-current-run i b k n γ m n≤m σ))
