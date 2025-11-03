{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.Constant.More
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Category
open Functor
open Functorᴰ
open Iso

-- What are the fundamental constructions on uncurried displayed presheaves?
--
-- 0. Change of base/reindexing by functors and by natural transformations
-- 1. Vertical Products (Unit, ×ⱽ)
-- 2. Exponentials
-- 3. Universal Quantifiers
module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {P : Presheaf D ℓP}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Pᴰ : Presheafᴰ' P Dᴰ ℓPᴰ)
  where
  reindPshᴰFunctor : Presheafᴰ' (reindPsh F P) Cᴰ ℓPᴰ
  reindPshᴰFunctor = reindPsh (Fᴰ /Fᴰ idPshHom) Pᴰ

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ} (α : PshHom P Q) (Qᴰ : Presheafᴰ' Q Cᴰ ℓQᴰ) where
  reindPshᴰNatTrans : Presheafᴰ' P Cᴰ ℓQᴰ
  reindPshᴰNatTrans = reindPsh (Idᴰ /Fⱽ α) Qᴰ

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  where
  UnitPshᴰ' : Presheafᴰ' P Cᴰ ℓ-zero
  UnitPshᴰ' = UnitPsh
  module _ (Pᴰ : Presheafᴰ' P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ' P Cᴰ ℓQᴰ) where
    _×ⱽPsh_ : Presheafᴰ' P Cᴰ (ℓ-max ℓPᴰ ℓQᴰ)
    _×ⱽPsh_ = Pᴰ ×Psh Qᴰ

    _⇒ⱽPshLarge_ : Presheafᴰ' P Cᴰ (ℓ-max
                                    (ℓ-max
                                     (ℓ-max (ℓ-max ℓC (ℓ-max ℓCᴰ ℓP)) (ℓ-max ℓC' (ℓ-max ℓCᴰ' ℓP)))
                                     (ℓ-max (ℓ-max ℓC' (ℓ-max ℓCᴰ' ℓP)) ℓPᴰ))
                                    ℓQᴰ)
    _⇒ⱽPshLarge_ = Pᴰ ⇒PshLarge Qᴰ

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  (P : Presheaf D ℓP)
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where
  UnitPshᴰ-reindPshᴰFunctor :
    PshIsoⱽ' (reindPshᴰFunctor Fᴰ (UnitPshᴰ' {Cᴰ = Dᴰ}{P = P}))
             (UnitPshᴰ' {Cᴰ = Cᴰ})
  UnitPshᴰ-reindPshᴰFunctor = pathToPshIso $
    sym $ Constant-natural (SET ℓ-zero) (Unit , isSetUnit) _

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  {F : Functor (Dᴰ / Q) (Cᴰ / P)}
  (Pᴰ : Presheafᴰ' P Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ' P Cᴰ ℓQᴰ)
  where
  ×ⱽPsh-reindPshFunctor :
    PshIsoⱽ' (reindPsh F (Pᴰ ×ⱽPsh Qᴰ))
             (reindPsh F Pᴰ ×ⱽPsh reindPsh F Qᴰ)
  ×ⱽPsh-reindPshFunctor = pathToPshIso $
    -- (×Sets ∘ (Pᴰ ,F Qᴰ)) ∘ ~Fᴰ
    (sym $ F-assoc)
    -- ×Sets ∘ ((Pᴰ ,F Qᴰ) ∘ ~Fᴰ)
    ∙ cong (×Sets ∘F_) ,F-natural
    -- ×Sets ∘ (Pᴰ ∘ ~Fᴰ ,F Qᴰ ∘ ~Fᴰ)
