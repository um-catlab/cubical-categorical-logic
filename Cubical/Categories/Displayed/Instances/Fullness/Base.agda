{-
  Fullness of a functor as a displayed category.

  For a functor F : C → D, the "FullnessOver" displayed category over C
  has as its fiber over y the property that F-hom is surjective at y:
    ∀ x → (f : D [ F x , F y ]) → ∃[ g ∈ C [ x , y ] ] F g ≡ f

  This is a PropertyOver with contractible homs.

  Universal property: a global section of FullnessOver is isFull F.
-}
module Cubical.Categories.Displayed.Instances.Fullness.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Constructions.PropertyOver

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor
open Section

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) where

  FullnessProperty : C .ob → Type (ℓ-max (ℓ-max ℓC ℓC') ℓD')
  FullnessProperty y =
    ∀ x → (f : D [ F ⟅ x ⟆ , F ⟅ y ⟆ ]) → ∃[ g ∈ C [ x , y ] ] F ⟪ g ⟫ ≡ f

  FullnessOver : Categoryᴰ C _ _
  FullnessOver = PropertyOver C FullnessProperty

  hasContrHomsFullnessOver : hasContrHoms FullnessOver
  hasContrHomsFullnessOver = hasContrHomsPropertyOver C FullnessProperty

  FullnessReflection : GlobalSection FullnessOver → isFull F
  FullnessReflection s x y f = s .F-obᴰ y x f

  FullnessIntroS : isFull F → GlobalSection FullnessOver
  FullnessIntroS full =
    mkContrHomsSection hasContrHomsFullnessOver (λ y x f → full x y f)
