{-# OPTIONS --lossy-unification #-}
{- TODO: split up this file into a bunch of individual construction files -}

{-

  Every construction on presheaves should come with
  1. A UMP which provides an interface to it
  2. A reindexing lemma that shows that it commutes with reindPshᴰNatTrans in the appropriate sense

-}

module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Sigma.More as Type
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.Reind
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.Constant.More
open import Cubical.Categories.FunctorComprehension.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory as TotalCat hiding (intro)
open import Cubical.Categories.HLevels
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions hiding (ΣPsh)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions.RightAdjoint
open import Cubical.Categories.Profunctor.Constructions.Extension
open import Cubical.Categories.Yoneda.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
import Cubical.Categories.Displayed.Presheaf.Constructions.Curry as Curry
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓS ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ ℓSᴰ : Level

open Category
open Functor
open Functorᴰ
open Iso
open PshHom
open PshIso

-- Products
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  module _ {P : Presheaf C ℓP} where
    LiftPshᴰ : Presheafᴰ P Cᴰ ℓPᴰ → (ℓPᴰ' : Level) → Presheafᴰ P Cᴰ (ℓ-max ℓPᴰ ℓPᴰ')
    LiftPshᴰ Pᴰ ℓPᴰ' = LiftF {ℓ' = ℓPᴰ'} ∘F Pᴰ

    UnitPshᴰ : Presheafᴰ P Cᴰ ℓ-zero
    UnitPshᴰ = UnitPsh
    module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where
      _×ⱽPsh_ : Presheafᴰ P Cᴰ (ℓ-max ℓPᴰ ℓQᴰ)
      _×ⱽPsh_ = Pᴰ ×Psh Qᴰ

      _⇒ⱽPshLarge_ : Presheafᴰ P Cᴰ (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓP) ℓPᴰ) ℓQᴰ)
      _⇒ⱽPshLarge_ = Pᴰ ⇒PshLarge Qᴰ

    -- TODO: rename: This is not weakening, wkLR∀ is.
    wkPshᴰ : (Q : Presheaf C ℓQ) → Functor (PresheafᴰCategory P Cᴰ ℓPᴰ) (PresheafᴰCategory (P ×Psh Q) Cᴰ ℓPᴰ)
    wkPshᴰ Q = reindPshF (Idᴰ /Fⱽ π₁ P Q)

    wkPshᴰ-cocont : (Q : Presheaf C ℓQ) → CoContinuous {C = (Cᴰ / P)}{D = Cᴰ / (P ×Psh Q)} (wkPshᴰ Q)
    wkPshᴰ-cocont Q = reindPshF-cocont (Idᴰ /Fⱽ π₁ P Q)

    module _ {Q : Presheaf C ℓQ} where
      private
        module ∀PshLarge = P⇒Large-cocontinuous (wkPshᴰ Q) (wkPshᴰ-cocont Q)
      module _ (PQᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ) where
        ∀PshLarge : Presheafᴰ P Cᴰ _
        ∀PshLarge = ∀PshLarge.P⇒Large PQᴰ

        -- Rᴰ(p) ⊢ ∀[ q ] PQᴰ(p,q) ≅ Rᴰ(p) ⊢ PQᴰ(p,q)
        ∀PshLarge-UMP : ∀ {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
          → Iso (PshHomⱽ Rᴰ ∀PshLarge) (PshHomⱽ (wkPshᴰ Q ⟅ Rᴰ ⟆) PQᴰ)
        ∀PshLarge-UMP = ∀PshLarge.P⇒Large-UMP PQᴰ _

  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    where
    _×ᴰPsh_ : (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
      → Presheafᴰ (P ×Psh Q) Cᴰ (ℓ-max ℓPᴰ ℓQᴰ)
    Pᴰ ×ᴰPsh Qᴰ = reindPshᴰNatTrans (π₁ P Q) Pᴰ ×ⱽPsh reindPshᴰNatTrans (π₂ P Q) Qᴰ
