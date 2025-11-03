{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Representable where

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
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
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
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Curry
open import Cubical.Categories.Displayed.Presheaf.Representable

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
open PshIso
open Iso

module _ {C : Category ℓC ℓC'}{x : C .ob} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Fibers Cᴰ
  _[-][-,_]' : Cᴰ.ob[ x ] → Presheafⱽ' x Cᴰ ℓCᴰ'
  _[-][-,_]' xᴰ = UncurryPshᴰ (C [-, x ]) Cᴰ (Cᴰ [-][-, xᴰ ])

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {x : C .Category.ob} (Pⱽ : Presheafⱽ' x Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Pⱽ = Presheafᴰ'Notation Cᴰ _ Pⱽ
  yoRecⱽ' : ∀ {xᴰ} → Pⱽ.p[ C.id ][ xᴰ ] → PshHomⱽ' (Cᴰ [-][-, xᴰ ]') Pⱽ
  yoRecⱽ' pⱽ = UncurryPshHomⱽ _ _ (yoRecⱽ (CurryPshⱽ Cᴰ Pⱽ) pⱽ)
    ⋆PshHomⱽ' pathToPshIso (CurryPshᴰIso _ Cᴰ .leftInv _) .trans

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         (x : C .Category.ob) (Pⱽ : Presheafⱽ' x Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module Pⱽ = Presheafᴰ'Notation Cᴰ (C [-, x ]) Pⱽ

  record UniversalElementⱽ'
    : Type (ℓ-max ℓC $ ℓ-max ℓC' $ ℓ-max ℓCᴰ $ ℓ-max ℓCᴰ' $ ℓPᴰ) where
    field
      vertexⱽ : Cᴰ.ob[ x ]
      elementⱽ : Pⱽ.p[ C.id ][ vertexⱽ ]
      universalⱽ : isPshIsoⱽ' (Cᴰ [-][-, vertexⱽ ]') Pⱽ (yoRecⱽ' Pⱽ elementⱽ)

    toPshIsoⱽ' : PshIsoⱽ' (Cᴰ [-][-, vertexⱽ ]') Pⱽ
    toPshIsoⱽ' = pshiso (yoRecⱽ' Pⱽ elementⱽ) universalⱽ

  -- fromPshIsoⱽ' : ∀ {v}
  --   → PshIsoⱽ' (Cᴰ [-][-, v ]') Pⱽ
  --   → UniversalElementⱽ'
  -- fromPshIsoⱽ' {v} α = {!!}

  Representableⱽ' : Type _
  Representableⱽ' = Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] PshIsoⱽ' (Cᴰ [-][-, xᴰ ]') Pⱽ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {x}
  {Pⱽ : Presheafⱽ' x Cᴰ ℓPᴰ}{Qⱽ : Presheafⱽ' x Cᴰ ℓQᴰ}
  where
  _◁PshIsoⱽ'_ : Representableⱽ' Cᴰ x Pⱽ → PshIsoⱽ' Pⱽ Qⱽ → Representableⱽ' Cᴰ x Qⱽ
  (xᴰ , α) ◁PshIsoⱽ' β = (xᴰ , (α ⋆PshIso β))

