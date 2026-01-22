{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-# OPTIONS --lossy-unification #-}

-- Common infrastructure for simply typed variables and contexts

module Cubical.Categories.WithFamilies.Simple.Instances.Free.Variable where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More

open import Cubical.Data.FinData hiding (elim)
open import Cubical.Data.List hiding (elim; [_])
open import Cubical.Data.List.FinData
open import Cubical.Data.List.Dependent
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' ℓC ℓC' ℓT ℓT' : Level

module _ (Ty : Type ℓ) where
  Ctx = List Ty
  data Var : Ctx → Ty → Type ℓ where
    vz : ∀ {Γ A} → Var (A ∷ Γ) A
    vs : ∀ {Γ A B} → Var Γ A → Var (B ∷ Γ) A

  AnyVar : (Γ : Ctx) → Type ℓ-zero
  AnyVar Γ = Fin (length Γ)

  FinVar : (Γ : Ctx) → (A : Ty) → Type ℓ
  FinVar Γ A = fiber (lookup Γ) A

  Var→FinVar : ∀ {Γ A} → Var Γ A → FinVar Γ A
  Var→FinVar vz = zero , refl
  Var→FinVar (vs x) = (suc $ finX .fst) , finX .snd where
    finX = Var→FinVar x

  FinVar→Var : ∀ {Γ A} → FinVar Γ A → Var Γ A
  FinVar→Var {Γ = B ∷ Γ}{A} (zero , B≡A) = subst (λ B → Var (B ∷ Γ) A) (sym B≡A) vz
  FinVar→Var {Γ = B ∷ Γ}{A} (suc x' , x':A) = vs (FinVar→Var (x' , x':A))

  VarRetractFinVar : ∀ {Γ A} (x : Var Γ A) → FinVar→Var (Var→FinVar x) ≡ x
  VarRetractFinVar vz = transportRefl vz
  VarRetractFinVar (vs x) = cong vs (VarRetractFinVar x)

  isSetFinVar : ∀ {Γ A} → isGroupoid Ty → isSet (FinVar Γ A)
  isSetFinVar isGpdTy = isSetΣ isSetFin (λ _ → isGpdTy _ _)

  isSetVar : ∀ {Γ A} → isGroupoid Ty → isSet (Var Γ A)
  isSetVar isGpdTy = isSetRetract Var→FinVar FinVar→Var VarRetractFinVar (isSetFinVar isGpdTy)
