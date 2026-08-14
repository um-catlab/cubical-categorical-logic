{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Monad.Instances.LocalState.Staton.Intrinsic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.FinData.Properties
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Functions.Embedding

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Injections
open import Cubical.Categories.Instances.Schanuel
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Pullback.More

open Category
open Cospan
open Functor

-- The underlying world functor of Staton's nominal set of atoms.
-- This is the covariant representable Inj [ 1 , - ].
AtomsFunctor : Functor Inj (SET ℓ-zero)
AtomsFunctor .F-ob n = Fin n , isSetFin
AtomsFunctor .F-hom f = f .fst
AtomsFunctor .F-id = refl
AtomsFunctor .F-seq f g = refl

point : {n : ℕ} → Fin n → Injection 1 n
point x .fst _ = x
point x .snd = isEmbedding-isProp→isSet
  (isContr→isProp isContrFin1) isSetFin _

Atoms-preservesPullbacks :
  PreservesPullbacks {C = Inj} {D = SET ℓ-zero} AtomsFunctor
Atoms-preservesPullbacks {s} {c} {p₁} {p₂} {commutes} pb {d} h k H =
  uniqueExists mediator
    ( (funExt λ x →
        funExt⁻ (cong fst (cone x .fst .snd .fst)) zero)
    , (funExt λ x →
        funExt⁻ (cong fst (cone x .fst .snd .snd)) zero))
    (λ _ → isProp×
      ((isSet→ isSetFin) _ _)
      ((isSet→ isSetFin) _ _))
    λ mediator' equations → funExt λ x →
      cong (λ q → q .fst .fst zero)
        (cone x .snd
          ( point (mediator' x)
          , injection≡ {n = 1} {m = s .l}
              (funExt λ _ → funExt⁻ (equations .fst) x)
          , injection≡ {n = 1} {m = s .r}
              (funExt λ _ → funExt⁻ (equations .snd) x)))
  where
  singletonCommutes : (x : ⟨ d ⟩) →
    point (h x) ⋆⟨ Inj ⟩ s .s₁ ≡ point (k x) ⋆⟨ Inj ⟩ s .s₂
  singletonCommutes x =
    injection≡ {n = 1} {m = s .m}
      (funExt λ _ → funExt⁻ H x)

  cone : (x : ⟨ d ⟩) →
    ∃![ q ∈ Injection 1 c ]
      (point (h x) ≡ q ⋆⟨ Inj ⟩ p₁) ×
      (point (k x) ≡ q ⋆⟨ Inj ⟩ p₂)
  cone x = pb {d = 1}
    (point (h x)) (point (k x)) (singletonCommutes x)

  mediator : ⟨ d ⟩ → Fin c
  mediator x = cone x .fst .fst .fst zero

-- Staton's atom object in the Schanuel topos.
Atoms : Schanuel ℓ-zero .ob
Atoms .fst = AtomsFunctor
Atoms .snd {s} {c} {p₁} {p₂} {commutes} pb =
  Atoms-preservesPullbacks
    {s = s} {c = c} {p₁ = p₁} {p₂ = p₂} {commutes = commutes} pb
