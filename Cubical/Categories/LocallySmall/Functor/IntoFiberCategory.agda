module Cubical.Categories.LocallySmall.Functor.IntoFiberCategory where


import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma


open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
import Cubical.Categories.LocallySmall.Functor.Base as LocallySmallF
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Instances.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Instances.Reindex.Properties

open Category
open Categoryᴰ
open SmallCategory

module FunctorDefs
  (C : SmallCategory ℓC ℓC')
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = SmallCategory C
    module D = Category D
    module Dᴰ = CategoryᴰNotation Dᴰ

  Functor : (d : Dob) → Typeω
  Functor d = LocallySmallF.Functor C.cat Dᴰ.v[ d ]

  module _ (D-⋆ : ∀ {x} → D.id D.⋆ D.id Eq.≡ D.id {x}) (d : Dob) where
    FunctorEq : Typeω
    FunctorEq = LocallySmallF.Functor C.cat (fibEq Dᴰ D-⋆ d)

    Functor→FunctorEq :
      Functor d → FunctorEq
    Functor→FunctorEq = fib→fibEq Dᴰ D-⋆ d LocallySmallF.∘F_

    FunctorEq→Functor :
      FunctorEq → Functor d
    FunctorEq→Functor = fibEq→fib Dᴰ D-⋆ d LocallySmallF.∘F_

  module FunctorNotation {d : Dob} (F : Functor d)
    where

    open LocallySmallF.FunctorNotation F public
