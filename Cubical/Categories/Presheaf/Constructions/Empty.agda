{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.Empty where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓP ℓQ ℓS : Level

open Functor
open PshHom

EmptyPsh : ∀ {C : Category ℓ ℓ'} → Presheaf C ℓ-zero
EmptyPsh = Constant _ _ (⊥ , (λ ()))

Empty*Psh : ∀ {C : Category ℓ ℓ'} {ℓ''} → Presheaf C ℓ''
Empty*Psh = Constant _ _ (⊥* , (λ ()))

EmptyPsh-elim : ∀ {C : Category ℓ ℓ'}{P : Presheaf C ℓA}
  → PshHom EmptyPsh P
EmptyPsh-elim .N-ob c ()
EmptyPsh-elim .N-hom c c' f ()
