module Cubical.Data.FinOrd.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Data.Nat
import Cubical.Data.Nat.Order.Recursive as Ord
import Cubical.Data.Fin as Fin
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Data.SumFin
open import Cubical.Data.FinSet.Base

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

isFinOrdLift :
  {L L' : Level} →
  {A : Type L} →
  isFinOrd A → isFinOrd (Lift {L}{L'} A)
fst (isFinOrdLift {A = A} isFinOrdA) = isFinOrdA .fst
snd (isFinOrdLift {A = A} isFinOrdA) =
  compEquiv (invEquiv LiftEquiv) (isFinOrdA .snd)
