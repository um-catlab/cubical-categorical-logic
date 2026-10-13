{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.IndexedProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓS : Level

open Functor
open PshHom


module _ {C : Category ℓC ℓC'}{X : Type ℓ} (P⟨x⟩ : X → Presheaf C ℓP) where
  private
    module P⟨x⟩ (x : X) = PresheafNotation (P⟨x⟩ x)
  ΠTyPsh : Presheaf C (ℓ-max ℓ ℓP)
  ΠTyPsh .F-ob c .fst = ∀ x → P⟨x⟩.p[_] x c
  ΠTyPsh .F-ob c .snd = isSetΠ (λ x → P⟨x⟩.isSetPsh x)
  ΠTyPsh .F-hom γ p⟨x⟩ x = P⟨x⟩ x .F-hom γ (p⟨x⟩ x)
  ΠTyPsh .F-id = funExt (λ p⟨x⟩ → funExt (λ x → P⟨x⟩.⋆IdL x (p⟨x⟩ x)))
  ΠTyPsh .F-seq f g = funExt (λ p⟨x⟩ → funExt λ x → P⟨x⟩.⋆Assoc x g f (p⟨x⟩ x))

  ΠTyPsh-app : ∀ x → PshHom ΠTyPsh (P⟨x⟩ x)
  ΠTyPsh-app x .N-ob = λ c z → z x
  ΠTyPsh-app x .N-hom c c' f p = refl

  ΠTyPsh-intro : {Q : Presheaf C ℓQ} → (∀ x → PshHom Q (P⟨x⟩ x)) → PshHom Q ΠTyPsh
  ΠTyPsh-intro α⟨x⟩ .N-ob = λ c z x → α⟨x⟩ x .N-ob c z
  ΠTyPsh-intro α⟨x⟩ .N-hom c c' f p = funExt (λ x → α⟨x⟩ x .N-hom c c' f p)
