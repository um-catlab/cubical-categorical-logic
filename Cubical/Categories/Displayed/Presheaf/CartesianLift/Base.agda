
module Cubical.Categories.Displayed.Presheaf.CartesianLift.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓQ ℓPᴰ ℓQᴰ : Level

open PshHom
open PshIso
open Category
open Functor
open Functorᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP}
         where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P

  CartesianLift : ∀ {x} (p : P.p[ x ]) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) → Type _
  CartesianLift p Pᴰ = UniversalElementⱽ Cᴰ _ (reindYo p Pᴰ)

  -- TODO: make this functorial
  -- i.e. an input displayed category over C whose objects are Σ[ c ] P.p[ c ] × Pᴰ

  module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    isFibration : Type _
    isFibration = ∀ {x} (p : P.p[ x ]) → CartesianLift p Pᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
         (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) (α : PshHom P Q)
         (isFibQᴰ : isFibration Qᴰ)
         where
  isFibrationReind : isFibration (reind {P = P} α Qᴰ)
  isFibrationReind p = isFibQᴰ (α .N-ob _ p) ◁PshIsoⱽ invPshIsoⱽ (reindYo-seqIsoⱽ α Qᴰ p)
