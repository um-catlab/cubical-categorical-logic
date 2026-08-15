module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.SetGetCommute where

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

{- A write and a read at distinct locations commute.

  set i b (get j (λ c → k c))
    = get j (λ c → set i b (k c))        when i ≢ j
-}
set-get-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref) → Distinctᵗ i j →
  (b : Γ ⊢ BoolVal) (k : Γ V.× BoolVal ⊢ T .F-ob A) →
  setᵗ i b (getᵗ j k) ≡
  getᵗ j (setᵗ (V.π₁ V.⋆ i) (V.π₁ V.⋆ b) k)
set-get-commuteᵗ {Γ = Γ} {A = A} i j i≢j b k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext {A = A} λ m n≤m σ →
    let
      γₘ = Γ .F-hom n≤m γ
      wi = weakenRef n≤m (i .N-ob n γ)
      wj = weakenRef n≤m (j .N-ob n γ)
      bv = b .N-ob n γ
      σi = updateStore {n = m} wi bv σ
      vj = lookupStore {n = m} wj σ
      iₘ = i .N-ob m γₘ
      ri = weakenRef ≤-refl iₘ
      bm = b .N-ob m γₘ
      ri≡wi = funExt⁻ (Ref .F-id) iₘ ∙ funExt⁻ (i .N-hom n≤m) γ
      bm≡bv = funExt⁻ (b .N-hom n≤m) γ
      store-right≡left = cong₂
        (λ r v → updateStore {n = m} r v σ) ri≡wi bm≡bv
    in
    setᵗ-run i b (getᵗ j k) n γ m n≤m σ
    ∙ getᵗ-run j k n γ m n≤m σi
    ∙ cong (λ v → k .N-ob m (γₘ , v) m ≤-refl σi)
        (lookup-update-diff {n = m} wi wj
          (weakenRef-distinct n≤m _ _ (i≢j n γ)) bv σ)
    ∙ cong (λ τ → k .N-ob m (γₘ , vj) m ≤-refl τ)
        (sym store-right≡left)
    ∙ sym (setᵗ-run (V.π₁ V.⋆ i) (V.π₁ V.⋆ b) k
        m (γₘ , vj) m ≤-refl σ)
    ∙ sym (getᵗ-run j
        (setᵗ (V.π₁ V.⋆ i) (V.π₁ V.⋆ b) k)
        n γ m n≤m σ))

------------------------------------------------------------------------
