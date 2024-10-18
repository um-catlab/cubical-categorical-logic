{-
  Definition of a natural transformation displayed over another natural transformation.
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.NaturalIsomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open NatIso
open NatTransᴰ
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  record NatIsoᴰ {F : Functor C D}{G : Functor C D}
    (α : NatIso F G)
    {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Gᴰ : Functorᴰ G Cᴰ Dᴰ)
    : Type (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ (ℓ-max ℓCᴰ' ℓDᴰ')))) where
    private
      module Cᴰ = Categoryᴰ Cᴰ
    field
      transᴰ : NatTransᴰ (α .trans) Fᴰ Gᴰ
      nIsoᴰ : ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → isIsoᴰ Dᴰ (α .nIso x) (transᴰ .N-obᴰ xᴰ)
      
