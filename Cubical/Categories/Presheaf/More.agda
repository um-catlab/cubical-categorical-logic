{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More

open Category
open Functor

private
  variable
    ℓ ℓ' ℓS ℓS' : Level

-- Isomorphism between presheaves of different levels
PshIso : (C : Category ℓ ℓ')
         (P : Presheaf C ℓS)
         (Q : Presheaf C ℓS') → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓS) ℓS')
PshIso {ℓS = ℓS}{ℓS' = ℓS'} C P Q =
  CatIso (FUNCTOR (C ^op) (SET (ℓ-max ℓS ℓS')))
    (LiftF {ℓ = ℓS}{ℓ' = ℓS'} ∘F P)
    (LiftF {ℓ = ℓS'}{ℓ' = ℓS} ∘F Q)

IdPshIso : (C : Category ℓ ℓ') (P : Presheaf C ℓS) → PshIso C P P
IdPshIso C P = idCatIso

𝓟o = Presheaf

𝓟* : Category ℓ ℓ' → (ℓS : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
𝓟* C ℓS = Functor C (SET ℓS)

module _ (C : Category ℓ ℓ') (c : C .ob) where
  open Category
  open UniversalElement

  selfUnivElt :  UniversalElement C (C [-, c ])
  selfUnivElt .vertex = c
  selfUnivElt .element = C .id
  selfUnivElt .universal A = isoToIsEquiv (iso _ (λ z → z)
    (C .⋆IdR)
    (C .⋆IdR))

  selfUnivEltᵒᵖ : UniversalElement (C ^op) (C [ c ,-])
  selfUnivEltᵒᵖ .vertex = c
  selfUnivEltᵒᵖ .element = C .id
  selfUnivEltᵒᵖ .universal _ = isoToIsEquiv (iso _ (λ z → z)
    (C .⋆IdL)
    (C .⋆IdL))

module _ {ℓo}{ℓh}{ℓp} (C : Category ℓo ℓh) (P : Presheaf C ℓp) where
  open UniversalElement

  UniversalElementOn : C .ob → Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  UniversalElementOn vertex =
    Σ[ element ∈ (P ⟅ vertex ⟆) .fst ] isUniversal C P vertex element

  UniversalElementToUniversalElementOn :
    (ue : UniversalElement C P) → UniversalElementOn (ue .vertex)
  UniversalElementToUniversalElementOn ue .fst = ue .element
  UniversalElementToUniversalElementOn ue .snd = ue .universal
