module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.SetSetSame where

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

{- A later write to the same location overwrites an earlier write.

  set i b (set i c t) = set i c t
-}
set-set-sameᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (b c : Γ ⊢ BoolVal) (t : Γ ⊢ T .F-ob A) →
  setᵗ i b (setᵗ i c t) ≡ setᵗ i c t
set-set-sameᵗ {Γ = Γ} {A = A} i b c t =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext {A = A} λ m n≤m σ →
    let
      r = weakenRef n≤m (i .N-ob n γ)
      bv = b .N-ob n γ
      cv = c .N-ob n γ
      σ' = updateStore {n = m} r bv σ
    in
    setᵗ-run {A = A} i b (setᵗ i c t) n γ m n≤m σ
    ∙ setᵗ-run {A = A} i c t n γ m n≤m σ'
    ∙ cong (t .N-ob n γ m n≤m)
        (update-overwrite {n = m} r bv cv σ)
    ∙ sym (setᵗ-run {A = A} i c t n γ m n≤m σ))
