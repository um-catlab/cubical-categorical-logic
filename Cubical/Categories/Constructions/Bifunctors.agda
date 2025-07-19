{-# OPTIONS --safe #-}
{-

  Category whose objects are bifunctors and morphisms are natural
  transformations.

-}
module Cubical.Categories.Constructions.Bifunctors where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.ChangeOfObjects as COO

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') (E : Category ℓE ℓE') where
  BIFUNCTOR : Category _ _
  BIFUNCTOR = ChangeOfObjects (FUNCTOR C (FUNCTOR D E)) CurryBifunctor

  CURRY-BIFUNCTOR : Functor BIFUNCTOR (FUNCTOR C (FUNCTOR D E))
  CURRY-BIFUNCTOR = COO.π _ CurryBifunctor

  open Functor
  open NatTrans
  UNCURRY-BIFUNCTOR : Functor (FUNCTOR C (FUNCTOR D E)) BIFUNCTOR
  UNCURRY-BIFUNCTOR .F-ob = CurriedToBifunctor
  UNCURRY-BIFUNCTOR .F-hom α = natTrans
    (λ x → natTrans (λ y → (α ⟦ x ⟧) ⟦ y ⟧) ((α ⟦ x ⟧) .N-hom))
    λ f → makeNatTransPath (funExt λ y → funExt⁻ (cong N-ob (α .N-hom _)) _)
  UNCURRY-BIFUNCTOR .F-id = makeNatTransPath refl
  UNCURRY-BIFUNCTOR .F-seq α β = makeNatTransPath refl
