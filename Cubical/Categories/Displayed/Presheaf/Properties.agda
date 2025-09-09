{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Equality.More
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section
import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Functor
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓPᴰ ℓQ ℓQᴰ : Level

open Functor
open Functorᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  TotalCatYoPshIso :
    ∀ {c} {cᴰ : Cᴰ.ob[ c ]} →
    PshIso (∫P (Cᴰ [-][-, cᴰ ])) ((TotalCat.∫C Cᴰ) [-, c , cᴰ ])
  TotalCatYoPshIso = eqToPshIso _ Eq.refl Eq.refl

  TotalCat×PshYoIso :
    ∀ {c d} {cᴰ : Cᴰ.ob[ c ]}{dᴰ : Cᴰ.ob[ d ]} →
    PshIso
      (∫P (Cᴰ [-][-, cᴰ ]) ×Psh ∫P (Cᴰ [-][-, dᴰ ]))
      (BinProductProf (TotalCat.∫C Cᴰ) .F-ob (((c , cᴰ)) , ((d , dᴰ))))
  TotalCat×PshYoIso = eqToPshIso _ Eq.refl Eq.refl
