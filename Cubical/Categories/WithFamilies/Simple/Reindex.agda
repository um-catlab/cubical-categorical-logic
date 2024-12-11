{-# OPTIONS --safe #-}
module Cubical.Categories.WithFamilies.Simple.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Constructions.TotalCategory.Limits
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.WithFamilies.Simple.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Constructions.Reindex.Limits
  hiding (reindex)
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
import Cubical.Categories.Displayed.Presheaf.CartesianLift as Presheafᴰ

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Displayed

private
  variable
    ℓC ℓC' ℓT ℓT' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level
    ℓD ℓD' ℓS ℓS' ℓDᴰ ℓDᴰ' ℓSᴰ ℓSᴰ' : Level

open UniversalElement
open UniversalElementᴰ
open isIsoOver
open Iso
open Presheafᴰ.CartesianLift

module _ {C : SCwF ℓC ℓC' ℓT ℓT'}
         {D : SCwF ℓD ℓD' ℓS ℓS' }
         (Dⱽ : SCwFⱽ D ℓDᴰ ℓDᴰ' ℓSᴰ ℓSᴰ')
         (F : PreMorphism C D)
       where
  opaque
    reindex : SCwFⱽ C ℓDᴰ ℓDᴰ' ℓSᴰ ℓSᴰ'
    reindex .fst = Reindex.reindex (Dⱽ .fst) (F .fst)
    reindex .snd .fst A = Dⱽ .snd .fst (F .snd .fst A)
    reindex .snd .snd .fst {A} Aᴰ = PshReind (Dⱽ .snd .snd .fst Aᴰ ∘Fᴰ (Reindex.π _ _ ^opFᴰ)) (F .snd .snd A)
    reindex .snd .snd .snd .fst = hasAllTerminalⱽReindex (Dⱽ .snd .snd .snd .fst)
    reindex .snd .snd .snd .snd .fst = isFibrationReindex (Dⱽ .fst) (F .fst) (Dⱽ .snd .snd .snd .snd .fst)
    reindex .snd .snd .snd .snd .snd .fst = hasAllBinProductⱽReindex (Dⱽ .snd .snd .snd .snd .snd .fst)
    reindex .snd .snd .snd .snd .snd .snd M FAᴰ =
      Presheafᴰ.hasAllCartesianLiftsPshReind _ _ (Presheafᴰ.reindexFunctorCartLifts (F .fst) (Dⱽ .snd .snd .fst FAᴰ) (λ p → Dⱽ .snd .snd .snd .snd .snd .snd p FAᴰ)) M
