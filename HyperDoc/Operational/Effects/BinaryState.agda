{-# OPTIONS --cubical --type-in-type #-}

module HyperDoc.Operational.Effects.BinaryState where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.FinData
import Cubical.Data.FinData as Fin
open import Cubical.Data.FinData.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import HyperDoc.Algebra.Base
open import HyperDoc.Operational.Effects.Reduction using (Polynomial; ⟦_⟧; mapP)
open import HyperDoc.Operational.Effects.MonadicReduction

open Polynomial
open Functor
open NatTrans
open IsMonad

State : Type
State = Bool

position : State → Fin 2
position false = zero
position true = suc zero

stateAt : Fin 2 → State
stateAt = Fin.rec false true

fin2-elim :
  ∀ {ℓ} (P : Fin 2 → Type ℓ) →
  P zero → P (suc zero) → (i : Fin 2) → P i
fin2-elim P p₀ p₁ i =
  subst P (Iso.ret finSucMaybeIso i) branch
  where
  branch : P (Iso.inv finSucMaybeIso (Iso.fun finSucMaybeIso i))
  branch with Iso.fun finSucMaybeIso i
  ... | nothing = p₀
  ... | just j =
    subst (λ k → P (suc k)) (isContrFin1 .snd j) p₁

BinaryStateP : Polynomial
BinaryStateP .Shape = Fin 2 → Fin 2
BinaryStateP .size _ = 2

shape-isSet : isSet (Shape BinaryStateP)
shape-isSet = isSetΠ (λ _ → isSetFin)

StateT : hSet ℓ-zero → hSet ℓ-zero
StateT = ⟦ BinaryStateP ⟧Set shape-isSet

η-state : ∀ {X : hSet ℓ-zero} → ⟨ X ⟩ → ⟨ StateT X ⟩
η-state x = (λ s → s) , (λ _ → x)

μ-state : ∀ {X : hSet ℓ-zero} → ⟨ StateT (StateT X) ⟩ → ⟨ StateT X ⟩
μ-state (σ , k) =
  ( (λ s → fst (k s) (σ s))
  , (λ s → snd (k s) (σ s))
  )

η-state-natural :
  NatTrans (𝟙⟨ SET ℓ-zero ⟩) (⟦ BinaryStateP ⟧Functor shape-isSet)
η-state-natural .N-ob X = η-state
η-state-natural .N-hom f = refl

μ-state-natural :
  NatTrans
    (funcComp
      (⟦ BinaryStateP ⟧Functor shape-isSet)
      (⟦ BinaryStateP ⟧Functor shape-isSet))
    (⟦ BinaryStateP ⟧Functor shape-isSet)
μ-state-natural .N-ob X = μ-state
μ-state-natural .N-hom f = refl

BinaryStateMonad :
  IsMonad (⟦ BinaryStateP ⟧Functor shape-isSet)
BinaryStateMonad .η = η-state-natural
BinaryStateMonad .μ = μ-state-natural
BinaryStateMonad .idl-μ =
  makeNatTransPathP F-rUnit refl
    (funExt λ X → funExt λ { (σ , xs) → refl })
BinaryStateMonad .idr-μ =
  makeNatTransPathP F-lUnit refl
    (funExt λ X → funExt λ { (σ , xs) → refl })
BinaryStateMonad .assoc-μ =
  makeNatTransPathP F-assoc refl
    (funExt λ X → funExt λ { (σ , xs) → refl })

data StateOp : Type where
  get : StateOp
  put : State → StateOp

StateΣ : Signature
StateΣ .Op = StateOp
StateΣ .arity get = 2
StateΣ .arity (put s) = 1

State-alg : (X : hSet ℓ-zero) → IsAlg StateΣ (StateT X)
State-alg X get args =
  ( (λ s → fst (args s) s)
  , (λ s → snd (args s) s)
  )
State-alg X (put s′) args =
  ( (λ _ → fst (args zero) (position s′))
  , (λ _ → snd (args zero) (position s′))
  )

map-state-alg :
  ∀ {X Y : hSet ℓ-zero} (f : ⟨ X ⟩ → ⟨ Y ⟩) →
  IsAlgHom
    {M = record { Carrier = StateT X ; interp = State-alg X }}
    {N = record { Carrier = StateT Y ; interp = State-alg Y }}
    (mapP f)
map-state-alg f get args = refl
map-state-alg f (put s) args = refl

μ-state-alg :
  (X : hSet ℓ-zero) →
  IsAlgHom
    {M = record { Carrier = StateT (StateT X)
                ; interp = State-alg (StateT X) }}
    {N = record { Carrier = StateT X ; interp = State-alg X }}
    μ-state
μ-state-alg X get args = refl
μ-state-alg X (put s) args = refl

module StateReduction =
  MonadicReduction
    StateΣ BinaryStateP shape-isSet BinaryStateMonad State-alg

VariableSet : hSet ℓ-zero
VariableSet = State , isSetBool

module Example =
  StateReduction.Terms
    map-state-alg μ-state-alg VariableSet

open Example
