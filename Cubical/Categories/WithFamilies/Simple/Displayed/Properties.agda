{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.Categories.WithFamilies.Simple.Displayed.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.HITs.GroupoidTruncation

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory
-- open import Cubical.Categories.Constructions.TotalCategory.Limits
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More renaming (preservesTerminal to funcPreservesTerminal)
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Displayed
open import Cubical.Categories.WithFamilies.Simple.Properties

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Terminal as Terminal
open import Cubical.Categories.Displayed.FunctorComprehension
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Limits.Terminal renaming (preservesTerminal to secPreservesTerminal)
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.Section
import Cubical.Categories.Displayed.Presheaf.CartesianLift as Presheafᴰ

private
  variable
    ℓC ℓC' ℓT ℓT' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level

open UniversalElement
open UniversalElementᴰ
open Functorᴰ
open isIsoOver
open Iso

module _
  (S : SCwF ℓC ℓC' ℓT ℓT')
  (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ')
  where
  open SCwFNotation S
  open SCwFᴰNotation S Sᴰ

  module _ {A : Ty}(Aᴰ : Tyᴰ A) where

    ExtendContextProfᴰ :
      Profunctorᴰ (ExtendContextProf A) Cᴰ Cᴰ {!!}
    ExtendContextProfᴰ .F-obᴰ Γᴰ = (Cᴰ [-][-, Γᴰ ]) ×ᴰPsh Tmᴰ Aᴰ
    ExtendContextProfᴰ .F-homᴰ fᴰ =
      PshHomᴰ→NatTransᴰ (PshHomEqPshHomᴰ (×ᴰ-introᴰ (×ᴰ-π₁ ⋆PshHomᴰ yoRecᴰ _ fᴰ) ×ᴰ-π₂) Eq.refl)
    ExtendContextProfᴰ .F-idᴰ =
      {!!}
    ExtendContextProfᴰ .F-seqᴰ = {!!}

    ExtendContextᴰ : Functorᴰ (ExtendContext A) (Sᴰ .fst) (Sᴰ .fst)
    ExtendContextᴰ = FunctorᴰComprehension ExtendContextProfᴰ (λ Γ Γᴰ → extᴰ Aᴰ Γᴰ)
