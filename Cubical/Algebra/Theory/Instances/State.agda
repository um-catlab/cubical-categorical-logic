-- The algebraic theory of a single mutable store.
module Cubical.Algebra.Theory.Instances.State where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Data.Sigma.More
open import Cubical.Functions.FunExtEquiv.More

open import Cubical.Algebra.Theory.Base

private
  variable
    ℓS ℓV ℓX ℓXᴰ ℓY ℓB ℓD ℓD' : Level

data StateOp {ℓS : Level} (Store : Type ℓS) : Type ℓS where
  read : StateOp Store
  write : Store → StateOp Store

StateSignature : (Store : Type ℓS) → Signature ℓS ℓS
StateSignature Store .Signature.Op = StateOp Store
StateSignature Store .Signature.Arity read = Store
StateSignature Store .Signature.Arity (write _) = Unit*

module StateSignature {s : Level} (Store : Type s) where
  open Signature (StateSignature Store) public

module _ (Store : Type ℓS) where
  open Signature (StateSignature Store)

  readTm : ∀ {V : Type ℓV}
    → (Store → |FreeAlgebra| V) → |FreeAlgebra| V
  readTm γ = app read γ

  writeTm : ∀ {V : Type ℓV}
    → Store → |FreeAlgebra| V → |FreeAlgebra| V
  writeTm s t = app (write s) (λ _ → t)

  data StateEq : Type ℓS where
    wt-rdEq : Store → StateEq
    rd-wtEq : StateEq
    wt-wtEq : Store → Store → StateEq

  StateEqArity : StateEq → Type ℓS
  StateEqArity (wt-rdEq _) = Store
  StateEqArity rd-wtEq = Unit*
  StateEqArity (wt-wtEq _ _) = Unit*

  StateLhs : (e : StateEq) → |FreeAlgebra| (StateEqArity e)
  StateLhs (wt-rdEq s) =
    writeTm s (readTm var)
  StateLhs rd-wtEq = var tt*
  StateLhs (wt-wtEq s s') =
    writeTm s (writeTm s' (var tt*))

  StateRhs : (e : StateEq) → |FreeAlgebra| (StateEqArity e)
  StateRhs (wt-rdEq s) = writeTm s (var s)
  StateRhs rd-wtEq = readTm (λ s → writeTm s (var tt*))
  StateRhs (wt-wtEq _ s') = writeTm s' (var tt*)

  StateTheory : Theory ℓS ℓS ℓS ℓS
  StateTheory .Theory.S = StateSignature Store
  StateTheory .Theory.Eq = StateEq
  StateTheory .Theory.EqArity = StateEqArity
  StateTheory .Theory.lhs = StateLhs
  StateTheory .Theory.rhs = StateRhs

module StateTheory {s : Level} (Store : Type s) where
  open Theory (StateTheory Store) public

module _ (Store : Type ℓS) (B : Theory.Model (StateTheory Store) ℓB) where
  StateModelRead : (Store → ⟨ B .fst ⟩) → ⟨ B .fst ⟩
  StateModelRead γ = B .snd .fst read γ

  StateModelWrite : Store → ⟨ B .fst ⟩ → ⟨ B .fst ⟩
  StateModelWrite s x = B .snd .fst (write s) (λ _ → x)

  StateModelWriteRead : (s : Store) (γ : Store → ⟨ B .fst ⟩) →
    StateModelWrite s (StateModelRead γ) ≡ StateModelWrite s (γ s)
  StateModelWriteRead s γ =
    B .snd .snd (wt-rdEq s) γ

  StateModelReadWrite : (x : ⟨ B .fst ⟩) →
    x ≡ StateModelRead (λ s → StateModelWrite s x)
  StateModelReadWrite x =
    B .snd .snd rd-wtEq (λ _ → x)

  StateModelWriteWrite : (s s' : Store) (x : ⟨ B .fst ⟩) →
    StateModelWrite s (StateModelWrite s' x) ≡ StateModelWrite s' x
  StateModelWriteWrite s s' x =
    B .snd .snd (wt-wtEq s s') (λ _ → x)

  StateModelReadRead : (γ : Store → Store → ⟨ B .fst ⟩) →
    StateModelRead (λ s → StateModelRead (γ s)) ≡
      StateModelRead (λ s → γ s s)
  StateModelReadRead γ =
    StateModelReadWrite (StateModelRead (λ s → StateModelRead (γ s)))
    ∙ cong StateModelRead
        (funExt λ s →
          StateModelWriteRead s (λ s' → StateModelRead (γ s'))
          ∙ StateModelWriteRead s (γ s)
          ∙ sym (StateModelWriteRead s (λ s' → γ s' s')))
    ∙ sym (StateModelReadWrite (StateModelRead (λ s → γ s s)))

  StateModelReadIdempotent : (x : ⟨ B .fst ⟩) →
    StateModelRead (λ _ → x) ≡ x
  StateModelReadIdempotent x =
    StateModelReadWrite (StateModelRead (λ _ → x))
    ∙ cong StateModelRead
        (funExt λ s → StateModelWriteRead s (λ _ → x))
    ∙ sym (StateModelReadWrite x)

module _ (Store : hSet ℓS) (X : hSet ℓX) where
  open Theory (StateTheory (Store .fst))

  StateFreeModel : Model (ℓ-max ℓS ℓX)
  StateFreeModel .fst =
    (Store .fst → Store .fst × X .fst)
    , isSetΠ λ _ → isSet× (Store .snd) (X .snd)
  StateFreeModel .snd .fst read γ s = γ s s
  StateFreeModel .snd .fst (write s) γ _ = γ tt* s
  StateFreeModel .snd .snd (wt-rdEq s) ρ =
    funExt λ _ → refl
  StateFreeModel .snd .snd rd-wtEq ρ =
    funExt λ _ → refl
  StateFreeModel .snd .snd (wt-wtEq s s') ρ =
    funExt λ _ → refl

  StateFreeModelη : X .fst → ⟨ StateFreeModel .fst ⟩
  StateFreeModelη x s = s , x

  module _ (B : Model ℓB) (f : X .fst → ⟨ B .fst ⟩) where
    StateFreeModelRec : Homo (Model→Algebra StateFreeModel) (Model→Algebra B)
    StateFreeModelRec .fst q =
      StateModelRead (Store .fst) B λ s →
        StateModelWrite (Store .fst) B (q s .fst) (f (q s .snd))
    StateFreeModelRec .snd read γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      StateModelReadRead (Store .fst) B
        (λ s s' →
          StateModelWrite (Store .fst) B
            (γ s s' .fst) (f (γ s s' .snd)))
      ∙ cong (StateFreeModelRec .fst) op∘γ≡op⟨γ⟩
    StateFreeModelRec .snd (write s) γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      StateModelWriteRead (Store .fst) B s
        (λ s' →
          StateModelWrite (Store .fst) B
            (γ tt* s' .fst) (f (γ tt* s' .snd)))
      ∙ StateModelWriteWrite (Store .fst) B s (γ tt* s .fst)
          (f (γ tt* s .snd))
      ∙ sym
          (StateModelReadIdempotent (Store .fst) B
            (StateModelWrite (Store .fst) B
              (γ tt* s .fst) (f (γ tt* s .snd))))
      ∙ cong (StateFreeModelRec .fst) op∘γ≡op⟨γ⟩

    StateFreeModelRec-β : (x : X .fst) →
      StateFreeModelRec .fst (StateFreeModelη x) ≡ f x
    StateFreeModelRec-β x =
      sym (StateModelReadWrite (Store .fst) B (f x))

  StateFreeModelRec-uniq :
    (B : Model ℓB)
    (f : Homo (Model→Algebra StateFreeModel) (Model→Algebra B))
    → f .fst ≡
      StateFreeModelRec B (λ x → f .fst (StateFreeModelη x)) .fst
  StateFreeModelRec-uniq B f = funExt λ q →
    sym
      ( cong (StateModelRead (Store .fst) B)
          (funExt λ s → f .snd (write _) _ _ refl)
      ∙ f .snd read _ _ refl)

  StateFreeModelUniversal : (B : Model ℓB) →
    isEquiv
      (λ (f : Homo (Model→Algebra StateFreeModel) (Model→Algebra B)) x →
        f .fst (StateFreeModelη x))
  StateFreeModelUniversal B = isIsoToIsEquiv
    ( StateFreeModelRec B
    , (λ f → funExt (StateFreeModelRec-β B f))
    , (λ f → Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ → B .fst .snd _ _)
        (sym (StateFreeModelRec-uniq B f)))
    )

-- An explicit characterization of the displayed free algebra
module _ (S : Type ℓS) where
  State : Type ℓX → Type (ℓ-max ℓS ℓX)
  State X = S → S × X

  mapState : {X : Type ℓX}{Y : Type ℓY} → (X → Y) → State X → State Y
  mapState f m s = m s .fst , f (m s .snd)

  Stateᴰ : (X : Type ℓX)(Xᴰ : X → Type ℓXᴰ) → State X → Type (ℓ-max ℓS ℓXᴰ)
  Stateᴰ X Xᴰ f = (s : S) → Xᴰ (f s .snd)

  module _ (X : Type ℓX)(Xᴰ : X → Type ℓXᴰ) where
    forget : State (Σ X Xᴰ) → State X
    forget = mapState fst

    StateFreeModelFiber : ∀ (f : State X)
      → Iso (fiber forget f)
            (Stateᴰ X Xᴰ f)
    StateFreeModelFiber f =
      fiber forget f
        Iso⟨ fiberPostcompIso (map-× (idfun S) fst) f ⟩
      ((s : S) → fiber (map-× (idfun S) fst) (f s))
        Iso⟨ codomainIsoDep (λ s →
          fiber (map-× (idfun S) fst) (f s)
            Iso⟨ invIso (fiber-map-idfun× fst _ _) ⟩
          fiber fst (f s .snd)
            Iso⟨ invIso (fiberProjIso _ Xᴰ _) ⟩
          Xᴰ (f s .snd)
            ∎Iso) ⟩
      Stateᴰ X Xᴰ f
        ∎Iso
