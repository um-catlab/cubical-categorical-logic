-- The algebraic theory of a read-only environment.
module Cubical.Algebra.Theory.Instances.Reader where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Functions.FunExtEquiv.More

open import Cubical.Algebra.Theory.Base

private
  variable
    ℓR ℓV ℓX ℓXᴰ ℓY ℓB ℓD ℓD' : Level

data ReaderOp : Type ℓ-zero where
  ask : ReaderOp

ReaderSignature : (Env : Type ℓR) → Signature ℓ-zero ℓR
ReaderSignature Env .Signature.Op = ReaderOp
ReaderSignature Env .Signature.Arity ask = Env

module ReaderSignature {r : Level} (Env : Type r) where
  open Signature (ReaderSignature Env) public

module _ (Env : Type ℓR) where
  private
    module S = Signature (ReaderSignature Env)

  askTm : ∀ {V : Type ℓV}
    → (Env → S.|FreeAlgebra| V) → S.|FreeAlgebra| V
  askTm γ = S.app ask γ

  data ReaderEq : Type ℓ-zero where
    ask-constEq : ReaderEq
    ask-askEq : ReaderEq

  ReaderEqArity : ReaderEq → Type ℓR
  ReaderEqArity ask-constEq = Unit*
  ReaderEqArity ask-askEq = Env × Env

  ReaderLhs : (e : ReaderEq) → S.|FreeAlgebra| (ReaderEqArity e)
  ReaderLhs ask-constEq = askTm (λ _ → S.var tt*)
  ReaderLhs ask-askEq =
    askTm (λ r → askTm (λ r' → S.var (r , r')))

  ReaderRhs : (e : ReaderEq) → S.|FreeAlgebra| (ReaderEqArity e)
  ReaderRhs ask-constEq = S.var tt*
  ReaderRhs ask-askEq = askTm (λ r → S.var (r , r))

  ReaderTheory : Theory ℓ-zero ℓR ℓ-zero ℓR
  ReaderTheory .Theory.S = ReaderSignature Env
  ReaderTheory .Theory.Eq = ReaderEq
  ReaderTheory .Theory.EqArity = ReaderEqArity
  ReaderTheory .Theory.lhs = ReaderLhs
  ReaderTheory .Theory.rhs = ReaderRhs

module ReaderTheory {r : Level} (Env : Type r) where
  open Theory (ReaderTheory Env) public

module _ (Env : Type ℓR) (X : hSet ℓX) where
  private
    module T = Theory (ReaderTheory Env)

  ReaderFreeModel : T.Model (ℓ-max ℓR ℓX)
  ReaderFreeModel .fst = (Env → X .fst) , isSetΠ λ _ → X .snd
  ReaderFreeModel .snd .fst ask γ r = γ r r
  ReaderFreeModel .snd .snd ask-constEq ρ =
    funExt λ _ → refl
  ReaderFreeModel .snd .snd ask-askEq ρ =
    funExt λ _ → refl

  ReaderFreeModelη : X .fst → ⟨ ReaderFreeModel .fst ⟩
  ReaderFreeModelη x _ = x

  module _ (B : T.Model ℓB) (f : X .fst → ⟨ B .fst ⟩) where
    ReaderFreeModelRec :
      T.Homo (T.Model→Algebra ReaderFreeModel) (T.Model→Algebra B)
    ReaderFreeModelRec .fst g =
      B .snd .fst ask (λ r → f (g r))
    ReaderFreeModelRec .snd ask γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      B .snd .snd ask-askEq
        (λ { (r , r') → f (γ r r') })
      ∙ cong (ReaderFreeModelRec .fst) op∘γ≡op⟨γ⟩

    ReaderFreeModelRec-β : (x : X .fst) →
      ReaderFreeModelRec .fst (ReaderFreeModelη x) ≡ f x
    ReaderFreeModelRec-β x =
      B .snd .snd ask-constEq (λ _ → f x)

  ReaderFreeModelRec-uniq :
    (B : T.Model ℓB)
    (f : T.Homo (T.Model→Algebra ReaderFreeModel) (T.Model→Algebra B))
    → f .fst ≡
      ReaderFreeModelRec B (λ x → f .fst (ReaderFreeModelη x)) .fst
  ReaderFreeModelRec-uniq B f = funExt λ g →
    sym
      (f .snd ask (λ r → ReaderFreeModelη (g r)) g refl)

  ReaderFreeModelUniversal : (B : T.Model ℓB) →
    isEquiv
      (λ (f : T.Homo (T.Model→Algebra ReaderFreeModel) (T.Model→Algebra B)) x →
        f .fst (ReaderFreeModelη x))
  ReaderFreeModelUniversal B = isIsoToIsEquiv
    ( ReaderFreeModelRec B
    , (λ f → funExt (ReaderFreeModelRec-β B f))
    , (λ f → Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ → B .fst .snd _ _)
        (sym (ReaderFreeModelRec-uniq B f)))
    )

-- An explicit characterization of the displayed free algebra
module _ (Env : Type ℓR) where
  Reader : Type ℓX → Type (ℓ-max ℓR ℓX)
  Reader X = Env → X

  mapReader : {X : Type ℓX}{Y : Type ℓY} → (X → Y) → Reader X → Reader Y
  mapReader f m e = f (m e)

  Readerᴰ : (X : Type ℓX)(Xᴰ : X → Type ℓXᴰ) → Reader X → Type (ℓ-max ℓR ℓXᴰ)
  Readerᴰ X Xᴰ f = (e : Env) → Xᴰ (f e)

  module _ (X : Type ℓX)(Xᴰ : X → Type ℓXᴰ) where
    forget : Reader (Σ X Xᴰ) → Reader X
    forget = mapReader fst

    ReaderFreeModelFiber : ∀ (f : Reader X)
      → Iso (fiber forget f)
            (Readerᴰ X Xᴰ f)
    ReaderFreeModelFiber f =
      fiber forget f
        Iso⟨ fiberPostcompIso fst f ⟩
      ((e : Env) → fiber fst (f e))
        Iso⟨ codomainIsoDep (λ e →
          fiber fst (f e)
            Iso⟨ invIso (fiberProjIso _ Xᴰ _) ⟩
          Xᴰ (f e)
            ∎Iso) ⟩
      Readerᴰ X Xᴰ f
        ∎Iso
