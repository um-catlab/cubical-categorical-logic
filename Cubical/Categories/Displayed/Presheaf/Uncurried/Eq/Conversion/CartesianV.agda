{-

  Uncurried Presheaves using EqElement
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV where

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

import Cubical.Categories.Displayed.Limits.CartesianV' as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Base as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions as Path

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓE ℓE' ℓEᴰ ℓEᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

module _ {C : Category ℓC ℓC'} (⋆AssocC : ReprEqAssoc C)(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  EqCCⱽ→CCⱽ : isCartesianⱽ ⋆AssocC Cᴰ → Path.CartesianCategoryⱽ C ℓCᴰ ℓCᴰ'
  EqCCⱽ→CCⱽ cartⱽCᴰ .Path.CartesianCategoryⱽ.Cᴰ = Cᴰ
  EqCCⱽ→CCⱽ cartⱽCᴰ .Path.CartesianCategoryⱽ.termⱽ x =
    EqReprⱽ→PathReprⱽ UnitⱽPsh (cartⱽCᴰ .fst x)
    Path.◁PshIsoⱽ {!!}
  EqCCⱽ→CCⱽ cartⱽCᴰ .Path.CartesianCategoryⱽ.bpⱽ xᴰ yᴰ =
    EqReprⱽ→PathReprⱽ ((Cᴰ [-][-, xᴰ ]) ×ⱽPsh (Cᴰ [-][-, yᴰ ])) (cartⱽCᴰ .snd .fst xᴰ yᴰ)
    Path.◁PshIsoⱽ {!!}
  EqCCⱽ→CCⱽ cartⱽCᴰ .Path.CartesianCategoryⱽ.cartesianLifts xᴰ x p =
    EqReprⱽ→PathReprⱽ _ (cartⱽCᴰ .snd .snd p xᴰ)
    Path.◁PshIsoⱽ {!!}
    
    -- {!EqReprⱽ→PathReprⱽ _ ?
    -- Path.◁PshIsoⱽ !}
