{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.Forall.Large.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation as NT
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.FunctorComprehension

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Functor
-- open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
-- open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Displayed.FunctorComprehension
-- import Cubical.Categories.Displayed.Presheaf.CartesianLift as PshᴰCL

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓ' ℓP ℓPᴰ ℓQ ℓQᴰ ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open NatTrans
open Functor
open Functorᴰ
open PshIso
open PshHom
open PshHomᴰ
open UniversalElementⱽ

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  where
  private
    module Cᴰ = Fibers Cᴰ
  open UniversalElement
  open UniversalElementⱽ

  -- A Presheafᴰ Q Cᴰ is just a Functorᴰ
  --
  -- Qᴰ : Cᴰ o-> Setᴰ
  -- Q  : C  o-> Set
  --
  -- is it equivalent to...
  -- x,xᴰ,q -> Set

  --

  -- I.e., the same as a section
  -- ∫ Cᴰ o→ Set over Q
  --
  -- PshHomᴰ (π₁ * P × q)

  --


  module _ {Q : Presheaf C ℓQ}(P : Presheaf C ℓP) where
    ∀PshLarge : (Pᴰ : Presheafᴰ (Q ×Psh P) Cᴰ ℓPᴰ) → Presheafᴰ Q Cᴰ _ -- (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓP) ℓPᴰ)
    ∀PshLarge QPᴰ = {!!}
    -- ∀Large : (Pᴰ : Presheafᴰ (Q ×Psh P) Cᴰ ℓPᴰ) → Presheafᴰ Q Cᴰ (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓP) ℓPᴰ)
    -- ∀Large  Pᴰ .F-obᴰ Γᴰ q .fst =
    --   PshHomᴰ (×PshIntro (π₁ (C [-, _ ]) P ⋆PshHom yoRec Q q) (π₂ (C [-, _ ]) P)) (reind (π₁ (C [-, _ ]) P) (Cᴰ [-][-, Γᴰ ])) Pᴰ
    -- ∀Large Pᴰ .F-obᴰ Γᴰ q .snd = isSetPshHomᴰ _ _ _
    -- ∀Large Pᴰ .F-homᴰ = {!!}
    -- ∀Large Pᴰ .F-idᴰ = {!!}
    -- ∀Large Pᴰ .F-seqᴰ = {!!}

  -- module _ {Q : Presheaf C ℓQ}((P , _×P) : LRPresheaf C ℓP)(π₁* : ∀ {Γ}(Γᴰ : Cᴰ.ob[ Γ ]) → CartesianLift Cᴰ Γᴰ ((Γ ×P) .element .fst))
  --   (Pᴰ : Presheafᴰ (Q ×Psh P) Cᴰ ℓPᴰ) where
  --   private
  --     module Q = PresheafNotation Q
  --     module Pᴰ = PresheafᴰNotation Pᴰ
  --   ∀Small : Presheafᴰ Q Cᴰ ℓPᴰ
  --   ∀Small .F-obᴰ {Γ} Γᴰ q .fst = Pᴰ.p[ ((Γ ×P) .element .fst Q.⋆ q) , (Γ ×P) .element .snd ][ π₁* Γᴰ .vertexⱽ ]
  --   ∀Small .F-obᴰ Γᴰ q .snd = Pᴰ.isSetPshᴰ
  --   ∀Small .F-homᴰ = {!!}
  --   ∀Small .F-idᴰ = {!!}
  --   ∀Small .F-seqᴰ = {!!}
