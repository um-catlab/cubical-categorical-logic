{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Presheaf.Power where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Bifunctor.Redundant

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Fibration.Base as Fibration
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Presheaf.CartesianLift as PshCartLift

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓQ ℓPᴰ ℓQᴰ : Level

open Category
open NatTrans
open Functorᴰ
open UniversalElementᴰ
open UniversalElementⱽ
open Fibration.CartesianLift
open PshCartLift.CartesianLift



-- module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
--          (isFibCᴰ : isFibration Cᴰ)
--          (bpⱽ : hasAllBinProductⱽ Cᴰ)
--   where
--   private
--     module Cᴰ = Categoryᴰ Cᴰ
--   Exponentialⱽ : ∀ {x} (xᴰ xᴰ' : Cᴰ.ob[ x ]) → Presheafⱽ Cᴰ x ℓCᴰ'
--   Exponentialⱽ xᴰ xᴰ' .F-obᴰ {z} zᴰ f =
--     Cᴰ [ f ][ bpⱽ (zᴰ , isFibCᴰ xᴰ f .f*yᴰ ) .vertexⱽ , xᴰ' ] , Cᴰ.isSetHomᴰ
--   Exponentialⱽ xᴰ xᴰ' .F-homᴰ = {!!}
--   Exponentialⱽ xᴰ xᴰ' .F-idᴰ = {!!}
--   Exponentialⱽ xᴰ xᴰ' .F-seqᴰ = {!!}

-- module _ {C : Category ℓC ℓC'}
--          (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
--          P : Presheaf C ℓP}
--          (Pᴰ : Presheafᴰ Cᴰ P ℓPᴰ)
--          (Qᴰ : Presheafᴰ Cᴰ P ℓQᴰ)
--          (isFibQᴰ : PshCartLift.hasAllCartesianLifts Qᴰ)
--          (bpⱽ : hasAllBinProductⱽ Cᴰ)
--   where
--   private
--     module Cᴰ = Categoryᴰ Cᴰ
--   Powerⱽ : Presheafᴰ Cᴰ P {!!}
--   Powerⱽ .F-obᴰ {z} zᴰ f = Qᴰ .F-obᴰ (bpⱽ (zᴰ , isFibQᴰ f .p*Pᴰ) .vertexⱽ) f
--   Powerⱽ .F-homᴰ fᴰ p qᴰ =
--     -- TODO: write this more understandably lol
--     Qᴰ .F-homᴰ (bpⱽ _ .elementⱽ .snd ⋆ⱽᴰ⟨ Cᴰ ⟩ isFibQᴰ p .isCartesian .fst (isFibQᴰ (P .Functor.F-hom _ p) .π)) p (isFibQᴰ p .π)
--   Powerⱽ .F-idᴰ = {!!}
--   Powerⱽ .F-seqᴰ = {!!}
