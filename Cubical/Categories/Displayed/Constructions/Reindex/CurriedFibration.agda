module Cubical.Categories.Displayed.Constructions.Reindex.CurriedFibration where

open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
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
