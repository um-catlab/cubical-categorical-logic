module Cubical.Categories.Instances.FinSets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function as Func
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors

open import Cubical.Categories.Category renaming (pathToIso to catPathToIso)
open import Cubical.Categories.WithFamilies.Simple
open import Cubical.Categories.WithFamilies.Simple.Instances.Democratic
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Instances.FinSets.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Constructions.FullSubcategory.More

open import Cubical.Categories.Displayed.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

open Categoryᴰ
open UniversalElement
open CartesianCategory

module _ ℓ where
  open FullSubcategory' (SET ℓ) isFinite
  TerminalFINSET : Terminal' (FINSET ℓ)
  TerminalFINSET = ∫termFull TerminalSET (isFinSetLift isFinSetUnit)

  BinProductsFINSET : BinProducts (FINSET ℓ)
  BinProductsFINSET = ∫bpFull BinProductsSET
    (λ fin fin' → isFinSet× (_ , fin) (_ , fin'))

  BinCoproductsFINSET : BinCoproducts (FINSET ℓ)
  BinCoproductsFINSET = ∫bcpFull BinCoproductsSET
    (λ fin fin' → isFinSet⊎ (_ , fin) (_ , fin'))

  InitialFINSET : Initial (FINSET ℓ)
  InitialFINSET = ∫initFull InitialSET (isFinSetLift isFinSet⊥)

  FINSETCartesianCategory : CartesianCategory _ ℓ
  FINSETCartesianCategory .C = FINSET _
  FINSETCartesianCategory .term = TerminalFINSET
  FINSETCartesianCategory .bp = BinProductsFINSET

  FINSET^opCartesianCategory : CartesianCategory _ ℓ
  FINSET^opCartesianCategory .C = FINSET^op _
  FINSET^opCartesianCategory .term = InitialFINSET
  FINSET^opCartesianCategory .bp = BinCoproductsFINSET

  FINSETSCwF : SCwF (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ
  FINSETSCwF = CartesianCategory→SCwF FINSETCartesianCategory

  FINSET^opSCwF : SCwF (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ
  FINSET^opSCwF = CartesianCategory→SCwF FINSET^opCartesianCategory
