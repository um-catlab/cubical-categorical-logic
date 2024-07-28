{-# OPTIONS --safe #-}
{-

  Category whose objects are bifunctors and morphisms are natural
  transformations.

-}
module Cubical.Categories.Constructions.Relators where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.ChangeOfObjects
open import Cubical.Categories.Constructions.Bifunctors
open import Cubical.Categories.Profunctor.Relator

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open NatTrans

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') ℓR where
  RELATOR : Category _ _
  RELATOR = BIFUNCTOR (C ^op) D (SET ℓR)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{ℓR}
  {P Q : C o-[ ℓR ]-* D}
  (ϕ : RELATOR C D ℓR [ P , Q ])
  where


  -- here we are defining a homomorphism of relators to basically
  -- consist of a natural family:
  relHomoAct : ∀ {x y} → P [ x , y ]R → Q [ x , y ]R
  relHomoAct {x}{y} = (ϕ ⟦ x ⟧) ⟦ y ⟧

  relHomoR : ∀ {c d d'} (g : D [ d , d' ])(p : P [ c , d ]R)
    → relHomoAct (p ⋆r⟨ P ⟩ g) ≡ (relHomoAct p) ⋆r⟨ Q ⟩ g
  relHomoR {c = c} g = funExt⁻ ((ϕ ⟦ c ⟧) .N-hom g)

  relHomoL : ∀ {c' c d} (f : C [ c' , c ])(p : P [ c , d ]R)
    → relHomoAct (f ⋆l⟨ P ⟩ p) ≡ f  ⋆l⟨ Q ⟩ relHomoAct p
  relHomoL {d = d} f = funExt⁻ (funExt⁻ (cong N-ob (ϕ .N-hom f)) d)

  -- however if we are aiming for maximum "redundancy" it would be
  -- more appropriate to include the following actions as well:
  -- ∀ {x y y'} → P [ x , y ]R → D [ y , y' ] → Q [ x , y' ]R
  -- ∀ {x' x y} → C [ x' , x ] → P [ x , y ]R → Q [ x' , y ]R
  -- ∀ {x' x y y'} → C [ x' , x ] → P [ x , y ]R → D [ y , y' ] → Q [ x' , y' ]R
