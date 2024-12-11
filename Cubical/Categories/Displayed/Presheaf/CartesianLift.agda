{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Presheaf.CartesianLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf
import Cubical.Categories.Displayed.Fibration.Base as Fibration

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓQ ℓPᴰ ℓQᴰ : Level

open Category
open Functor
open Functorᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP}
         where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  record CartesianLift {x : C .ob} (p : ⟨ P ⟅ x ⟆ ⟩) (Pᴰ : Presheafᴰ Cᴰ P ℓPᴰ) : Type
    (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') ℓPᴰ)) where
    field
      p*Pᴰ : Cᴰ.ob[ x ]
      π : ⟨ Pᴰ .F-obᴰ p*Pᴰ p ⟩
      isCartesian : ∀ {z zᴰ}{g : C [ z , x ]} →
        isIso (λ (gᴰ : Cᴰ [ g ][ zᴰ , p*Pᴰ ]) → Pᴰ .F-homᴰ gᴰ p π)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         where
  -- TODO: should we just define Fibration.CartesianLift this way?
  fibLift→PshᴰLift : ∀ {x y yᴰ}{f : C [ x , y ]}
    → Fibration.CartesianLift Cᴰ yᴰ f
    → CartesianLift f (Cᴰ [-][-, yᴰ ])
  fibLift→PshᴰLift = λ z →
                        record
                        { p*Pᴰ = z .Fibration.CartesianLift.f*yᴰ
                        ; π = z .Fibration.CartesianLift.π
                        ; isCartesian = z .Fibration.CartesianLift.isCartesian
                        }
