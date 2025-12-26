module Cubical.Categories.Displayed.Constructions.Reindex.CurriedFibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (F : Functor C D) where

  CartesianLiftReindex : ∀ {c c'}{dᴰ}{f : C [ c , c' ]} →
    CartesianLift Dᴰ dᴰ (F ⟪ f ⟫) →
    CartesianLift (reindex Dᴰ F) dᴰ f
  CartesianLiftReindex cL =
    reindUEⱽ cL ◁PshIsoⱽ
      (invPshIsoⱽ (reindYoReindFunc {F = F})
      ⋆PshIsoⱽ reindPshIsoⱽ (yoRec (C [-, _ ]) _) reindⱽFuncRepr)

  isFibrationReindex
    : isFibration Dᴰ
    → isFibration (reindex Dᴰ F)
  isFibrationReindex isFib xᴰ f =
    CartesianLiftReindex $ isFib xᴰ (F ⟪ f ⟫)
