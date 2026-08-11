module Cubical.Categories.Monad.Instances.LocalState.PlotkinPower.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary

open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Injections
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Constructions.Tensor

open import Cubical.Categories.Monad.Instances.LocalState.PlotkinPower.Base

open Functor

record LocalStateOperations {ℓV ℓA : Level}
  (V : hSet ℓV) (A : Functor Inj (SET ℓA))
  : Type (ℓ-max ℓV ℓA) where
  field
    lookup : (n : ℕ) → Fin n → (⟨ V ⟩ → ⟨ A ⟅ n ⟆ ⟩) → ⟨ A ⟅ n ⟆ ⟩
    update : (n : ℕ) → Fin n → ⟨ V ⟩ → ⟨ A ⟅ n ⟆ ⟩ → ⟨ A ⟅ n ⟆ ⟩
    allocate : (n : ℕ) → ⟨ V ⟩ → ⟨ A ⟅ suc n ⟆ ⟩ → ⟨ A ⟅ n ⟆ ⟩

module _ {ℓV : Level} (V : hSet ℓV)
  (A : Functor Inj (SET ℓV)) where

  freshInjection : (n : ℕ) → Injection n (suc n)
  freshInjection n = subst (Injection n)
    (+-suc n 0 ∙ cong suc (+-zero n))
    (extendInjection {n} {1})

  updateStore : {n : ℕ} → Fin n → ⟨ V ⟩ →
    (Fin n → ⟨ V ⟩) → Fin n → ⟨ V ⟩
  updateStore i v S j with discreteFin i j
  ... | yes _ = v
  ... | no _ = S j

  freshStore : {n : ℕ} → ⟨ V ⟩ →
    (Fin n → ⟨ V ⟩) → Fin (suc n) → ⟨ V ⟩
  freshStore {n} v S = subst (λ k → Fin k → ⟨ V ⟩)
    (+-suc n 0 ∙ cong suc (+-zero n))
    (S ++Fin (λ _ → v))

  hideFresh : (n : ℕ) →
    LocalStateAt V A (suc n) .fst → LocalStateAt V A n .fst
  hideFresh n = R₊.rec
    (LocalStateAt V A n .snd)
    (λ (a , f) S →
      (a , composeInjection (freshInjection n) f) R.,⊗ S)
    (λ (a , f) g S →
      R.swap (a , composeInjection (freshInjection n) f) g S
      ∙ cong (R._,⊗ S)
          (ΣPathP (refl , injection≡ refl)))
    where
    module R₊ = Tensor (Cov V A (suc n)) (Store V)
    module R = Tensor (Cov V A n) (Store V)

  T-operations : LocalStateOperations V (T V .F-ob A)
  T-operations .LocalStateOperations.lookup n i k S = k (S i) S
  T-operations .LocalStateOperations.update n i v t S =
    t (updateStore i v S)
  T-operations .LocalStateOperations.allocate n v t S =
    hideFresh n (t (freshStore v S))
