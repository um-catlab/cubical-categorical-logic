{-

  Enhancement of IsoFiber to a displayed monoidal category when the
  functor F : C → D is enhanced with strong monoidal structure

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.IsoFiber.Monoidal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Constructions.BinProduct.Monoidal
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.Instances.Arrow.Base hiding (Iso)
open import Cubical.Categories.Displayed.Instances.Arrow.Properties
open import Cubical.Categories.Displayed.Instances.Arrow.Monoidal
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Displayed.Constructions.Reindex.Monoidal
open import Cubical.Categories.Displayed.Constructions.TotalCategory.Monoidal
open import Cubical.Categories.Bifunctor hiding (Fst; Snd)

import      Cubical.Categories.Displayed.Constructions.IsoFiber.Base
  as |IsoFiber|


private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

module _ {M : MonoidalCategory ℓC ℓC'} {N : MonoidalCategory ℓD ℓD'}
  (G : StrongMonoidalFunctor M N)
  where

  IsoFiber : MonoidalCategoryᴰ N (ℓ-max ℓC ℓD') (ℓ-max ℓC' ℓD')
  IsoFiber = ∫Mᴰsr N M
    (reindex (Iso N) (IdStr ×F G)
      (hasPropHomsIso (MonoidalCategory.C N))
      (isIsoFibrationIso (MonoidalCategory.C N)))

  private
    test-defn :
      MonoidalCategoryᴰ.Cᴰ IsoFiber
      ≡ |IsoFiber|.IsoFiber (StrongMonoidalFunctor.F G)
    test-defn = refl
