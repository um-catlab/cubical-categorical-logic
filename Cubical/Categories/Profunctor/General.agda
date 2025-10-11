module Cubical.Categories.Profunctor.General where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Functor
open NatTrans

-- A profunctor, also called a distributor is a generalization of a
-- functor where the values are not objects of the codomain, but
-- instead presheaves
Profunctor : (C : Category ℓC ℓC')(D : Category ℓD ℓD') → ∀ ℓS → Type _
Profunctor C D ℓS = Functor C (PresheafCategory D ℓS)

module ProfunctorNotation {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (R : Profunctor C D ℓR) where
  private
    module C = Category C
    module D = Category D
    variable
      x x' x'' x''' : D.ob
      y y' y'' y''' : C.ob
    RBif : Bifunctor (D ^op) C (SET ℓR)
    RBif = Sym $ CurriedToBifunctor R
    module RBif = Bifunctor RBif
    -- ⋆IdLᶜᵖ
  Het[_,_] : (x : D.ob) (y : C.ob) → Type _
  Het[ x , y ] = ⟨ RBif.Bif-ob x y  ⟩
  _⋆ᵖᶜ_ : (h : Het[ x , y ])(g : C [ y , y' ]) → Het[ x , y' ]
  h ⋆ᵖᶜ g = RBif.Bif-homR _ g h
  _⋆ᶜᵖ_ : (f : D [ x , x' ])(h : Het[ x' , y ]) → Het[ x , y ]
  f ⋆ᶜᵖ h = RBif.Bif-homL f _ h

  opaque
    ⋆IdLᶜᵖ : (h : Het[ x , y ])
      → D.id ⋆ᶜᵖ h ≡ h
    ⋆IdLᶜᵖ = funExt⁻ RBif.Bif-L-id

    ⋆IdRᵖᶜ : (h : Het[ x , y ])
      → h ⋆ᵖᶜ C.id ≡ h
    ⋆IdRᵖᶜ = funExt⁻ RBif.Bif-R-id

    ⋆Assocᵖᶜᶜ : (h : Het[ x , y ])(g : C [ y , y' ])(g' : C [ y' , y'' ])
      → ((h ⋆ᵖᶜ g) ⋆ᵖᶜ g') ≡ (h ⋆ᵖᶜ (g C.⋆ g'))
    ⋆Assocᵖᶜᶜ h g g' = sym $ funExt⁻ (RBif.Bif-R-seq g g') h

    ⋆Assocᶜᶜᵖ : (f' : D [ x'' , x' ])(f : D [ x' , x ])(h : Het[ x , y ])
      → ((f' D.⋆ f) ⋆ᶜᵖ h) ≡ (f' ⋆ᶜᵖ (f ⋆ᶜᵖ h))
    ⋆Assocᶜᶜᵖ f' f h = funExt⁻ (RBif.Bif-L-seq f f') h

    ⋆Assocᶜᵖᶜ : (f : D [ x , x' ])(h : Het[ x' , y ])(g : C [ y , y' ])
      → ((f ⋆ᶜᵖ h) ⋆ᵖᶜ g) ≡ (f ⋆ᶜᵖ (h ⋆ᵖᶜ g))
    ⋆Assocᶜᵖᶜ f h g = funExt⁻ (R .F-hom g .N-hom f) h
module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') ℓS where
  PROFUNCTOR : Category _ _
  PROFUNCTOR = FUNCTOR C (PresheafCategory D ℓS)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (R : Profunctor C D ℓS) where

  UniversalElements : Type _
  UniversalElements =
    ∀ (c : C .ob)
    → UniversalElement D (R ⟅ c ⟆)
