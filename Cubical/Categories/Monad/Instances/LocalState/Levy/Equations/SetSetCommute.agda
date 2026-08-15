module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.SetSetCommute where

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

{- Writes to distinct locations commute.

  set i b (set j c t) = set j c (set i b t)    when i ≢ j
-}
set-set-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref) → Distinctᵗ i j →
  (b c : Γ ⊢ BoolVal) (t : Γ ⊢ T .F-ob A) →
  setᵗ i b (setᵗ j c t) ≡ setᵗ j c (setᵗ i b t)
set-set-commuteᵗ {Γ = Γ} {A = A} i j i≢j b c t =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext {A = A} λ m n≤m σ →
    let
      wi = weakenRef n≤m (i .N-ob n γ)
      wj = weakenRef n≤m (j .N-ob n γ)
      bv = b .N-ob n γ
      cv = c .N-ob n γ
    in
    setᵗ-run {A = A} i b (setᵗ j c t) n γ m n≤m σ
    ∙ setᵗ-run {A = A} j c t n γ m n≤m
        (updateStore {n = m} wi bv σ)
    ∙ cong (t .N-ob n γ m n≤m)
        (update-commute {n = m} wi wj
          (weakenRef-distinct n≤m _ _ (i≢j n γ)) bv cv σ)
    ∙ sym (setᵗ-run {A = A} i b t n γ m n≤m
        (updateStore {n = m} wj cv σ))
    ∙ sym (setᵗ-run {A = A} j c (setᵗ i b t) n γ m n≤m σ))
