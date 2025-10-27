{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.Restriction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt

private
  variable
    ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓS : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  where
  restrictPsh : (F : Functor C D) (P : Presheaf D ℓP) → Presheaf C ℓP
  restrictPsh F P = P ∘F (F ^opF)

  restrictPshHom : {P : Presheaf D ℓP}{Q : Presheaf D ℓQ}
    (F : Functor C D)(α : PshHom P Q)
    → PshHom (restrictPsh F P) (restrictPsh F Q)
  restrictPshHom F α = α ∘ˡ F
