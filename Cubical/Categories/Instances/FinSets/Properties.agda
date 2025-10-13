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
open import Cubical.Categories.WithFamilies.Simple.Displayed
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
open import Cubical.Categories.Displayed.Limits.Terminal renaming (preservesTerminal to secPreservesTerminal)
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf.Section
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Properties

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

  module isFreeSCwFFINSET^op {ℓC ℓC' ℓSᴰ ℓSᴰ'} (Sᴰ : SCwFᴰ FINSET^opSCwF ℓC ℓC' ℓSᴰ ℓSᴰ') where
    private
      module Sᴰ = SCwFᴰNotation Sᴰ
      module FINSET^op = SCwFNotation FINSET^opSCwF

    elimSection : GlobalSection Sᴰ.Cᴰ
    elimSection .Section.F-obᴰ A = {!!}
    elimSection .Section.F-homᴰ = {!!}
    elimSection .Section.F-idᴰ = {!!}
    elimSection .Section.F-seqᴰ = {!!}

    elimTy : (A : FINSET^op.Ty) → Sᴰ.Tyᴰ A
    elimTy A = {!!}

    elimPshSection :
      (A : FINSET^op.Ty) →
      PshSection elimSection (Sᴰ.Tmᴰ $ elimTy A)
    elimPshSection = {!!}

    elimPreservesTerminal : secPreservesTerminal elimSection InitialFINSET
    elimPreservesTerminal = {!!}

    elimPreservesExt : (A : FINSET^op.Ty) →
      preservesLocalRep ((Sᴰ.Tmᴰ $ elimTy A) , Sᴰ.extᴰ (elimTy A)) (elimPshSection A)
    elimPreservesExt = {!!}

    elimSCwFSection : SCwFSection FINSET^opSCwF Sᴰ
    elimSCwFSection = {!!}


  isFreeSCwFFINSET^op : isFreeSCwF FINSET^opSCwF
  isFreeSCwFFINSET^op Sᴰ = {!!}
