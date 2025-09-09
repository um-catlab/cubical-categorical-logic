{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Fibration.Manual where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Displayed.FunctorComprehension
import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.CartesianLift.Manual
  using () renaming (
    CartesianLift to PshᴰCartesianLift
  ; isFibration to PshᴰisFibration) public

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level


module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Fibers Cᴰ
    module C = Category C

  -- The Cartesian lifting of a displayed object yᴰ along f
  -- is precisely the data that Cᴰ [-][-, yᴰ ] has a
  -- Cartesian lift (of displayed presheaves) along
  -- f (viewed as an element of C [-, y ])
  CartesianLift :
    {x y : C.ob} (yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ]) → Type _
  CartesianLift yᴰ f = PshᴰCartesianLift f (Cᴰ [-][-, yᴰ ])

  isFibration : Type _
  isFibration =
    ∀ {c : C.ob} (cᴰ : Cᴰ.ob[ c ]) → PshᴰisFibration (Cᴰ [-][-, cᴰ ])
