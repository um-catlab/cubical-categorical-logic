{-

  Uncurried Presheaves using EqElement
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.HLevels
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions hiding (π₁Strict ; π₂Strict)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.StrictHom renaming (π₁ to π₁Strict ; π₂ to π₂Strict)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
import Cubical.Categories.Displayed.Instances.Sets.Base as Setᴰ
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq
import Cubical.Categories.Displayed.Presheaf.Base as Curried

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.Eq
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.Push

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓE ℓE' ℓEᴰ ℓEᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open isIsoOver
open NatTrans
open NatTransᴰ
open NatIso
open NatIsoᴰ
open PshHomEq
open PshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  module _
    {P : Presheaf C ℓP}
    {Q : Presheaf C ℓQ}
    (α : PshHomStrict P Q)
    (Pᴰ : Presheafᴰ Q Cᴰ ℓPᴰ)
    (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
    where
    *↑-×-commute' : PshIsoEq (α *↑ (Pᴰ ×ⱽPsh Qᴰ)) ((α *↑ Pᴰ) ×ⱽPsh (α *↑ Qᴰ))
    *↑-×-commute' .PshIsoEq.isos (c , cᴰ , p) = idIso
    *↑-×-commute' .PshIsoEq.nat = λ c c' f p' p z → z

  module _ {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
    (α : PshHomStrict P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) (Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ)
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    where
    *↑-×-commute : Iso (PshHomEq Pᴰ (α *↑ (Qᴰ ×ⱽPsh Rᴰ))) (PshHomEq Pᴰ ((α *↑ Qᴰ) ×ⱽPsh (α *↑ Rᴰ)))
    *↑-×-commute = postcompPshIsoEq (*↑-×-commute' _ _ _)

  module _ {ℓP ℓPᴰ : Level} where
    PSHᴰBPⱽ : BinProductsⱽ (PRESHEAFᴰ Cᴰ ℓP ℓPᴰ)
    PSHᴰBPⱽ Pᴰ Qᴰ .fst = Pᴰ ×ⱽPsh Qᴰ
    PSHᴰBPⱽ Pᴰ Qᴰ .snd .PshIsoEq.isos (R , Rᴰ , α) =
      PshHomEq Rᴰ (α *↑ (Pᴰ ×ⱽPsh Qᴰ))
        Iso⟨ *↑-×-commute α Pᴰ Qᴰ ⟩
      PshHomEq Rᴰ ((α *↑ Pᴰ) ×ⱽPsh (α *↑ Qᴰ))
        Iso⟨ ×PshEq-UMP (α *↑ Pᴰ) (α *↑ Qᴰ) ⟩
      (PshHomᴰ α Rᴰ Pᴰ) × (PshHomᴰ α Rᴰ Qᴰ)
      ∎Iso
    PSHᴰBPⱽ Pᴰ Qᴰ .snd .PshIsoEq.nat _ _ (_ , _ , Eq.refl) _ _ Eq.refl =
      Eq.pathToEq (ΣPathP (makePshHomEqPath refl , makePshHomEqPath refl))
