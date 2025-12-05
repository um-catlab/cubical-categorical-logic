module Cubical.Categories.LocallySmall.Functor.SmallFibers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
import Cubical.Categories.Functor as SmallFunctor
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
import Cubical.Categories.LocallySmall.Functor.Base as LocallySmallF
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Properties

open Category
open Categoryᴰ
open SmallCategory

module _
  {C : SmallCategory ℓC ℓC'}
  {D : SmallCategory ℓD ℓD'}
  where
  private
    module C = SmallCategory C
    module D = SmallCategory D
  module FunctorDefs
    {Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ}
    (Cᴰ : SmallFibersCategoryᴰ C.cat Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ)
    {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
    (Dᴰ : SmallFibersCategoryᴰ D.cat Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
    where
    private
      module Cᴰ = CategoryᴰNotation Cᴰ
      module Dᴰ = CategoryᴰNotation Dᴰ

    Functor : (c : C.ob) → (d : D.ob) → Typeω
    Functor c d = LocallySmallF.Functor Cᴰ.v[ liftω c ] Dᴰ.v[ liftω d ]

    module FunctorNotation {c : C.ob} {d : D.ob} (F : Functor c d)
      where

      open LocallySmallF.FunctorNotation F public
