{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Functor.More where


open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' : Level


module _ {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} where
  open Functor
  open Functorᴰ

  weakenF : {D : Category ℓD ℓD'} {E : Category ℓE ℓE'} {F : Functor B C}
          → (G : Functor D E)
          → Functorᴰ F (weaken B D) (weaken C E)
  weakenF G .F-obᴰ = G .F-ob
  weakenF G .F-homᴰ = G .F-hom
  weakenF G .F-idᴰ = G .F-id
  weakenF G .F-seqᴰ = G .F-seq
