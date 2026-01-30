{-

  Uncurried Presheaves using EqElement
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
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
import Cubical.Categories.Displayed.Presheaf.Uncurried.Base as Path

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓE ℓE' ℓEᴰ ℓEᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  Path/→Eq/ : Functor (Cᴰ Path./ P) (Cᴰ / P)
  Path/→Eq/ = ∫F {F = Id} (Idᴰ ×ᴰF Element→EqElement P)

  Eq/→Path/ : Functor (Cᴰ / P) (Cᴰ Path./ P)
  Eq/→Path/ = ∫F {F = Id} (Idᴰ ×ᴰF EqElement→Element P)

  EqPresheafᴰ→PathPresheafᴰ : Presheafᴰ P Cᴰ ℓPᴰ → Path.Presheafᴰ P Cᴰ ℓPᴰ
  EqPresheafᴰ→PathPresheafᴰ = reindPsh Path/→Eq/

  PathPresheafᴰ→EqPresheafᴰ : Path.Presheafᴰ P Cᴰ ℓPᴰ → Presheafᴰ P Cᴰ ℓPᴰ
  PathPresheafᴰ→EqPresheafᴰ = reindPsh Eq/→Path/
