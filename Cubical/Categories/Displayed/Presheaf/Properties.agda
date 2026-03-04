{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Properties where


import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Instances.TotalCategory as TotalCat
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base

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
