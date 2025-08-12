{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
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

open Functor

private
  variable
    ℓ ℓ' ℓS ℓS' : Level

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

module _ (C : Category ℓ ℓ') (c : C .Category.ob) where
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
  open Category
  UniversalElementOn : C .ob → Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  UniversalElementOn vertex =
    Σ[ element ∈ (P ⟅ vertex ⟆) .fst ] isUniversal C P vertex element

  UniversalElementToUniversalElementOn :
    (ue : UniversalElement C P) → UniversalElementOn (ue .vertex)
  UniversalElementToUniversalElementOn ue .fst = ue .element
  UniversalElementToUniversalElementOn ue .snd = ue .universal

-- Natural transformation between presheaves of different levels
module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓS)(Q : Presheaf C ℓS') where
  private
    module C = Category C
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  PshHom : Type _
  PshHom = Σ[ α ∈ (∀ (x : C.ob) → P.p[ x ] → Q.p[ x ]) ]
    (∀ x y (f : C [ x , y ]) (p : P.p[ y ])→
     α x (f P.⋆ p) ≡ (f Q.⋆ α y p))

  isPropN-hom : ∀ (α : (∀ (x : C.ob) → P.p[ x ] → Q.p[ x ])) →
    isProp (∀ x y (f : C [ x , y ]) (p : P.p[ y ])→
     α x (f P.⋆ p) ≡ (f Q.⋆ α y p))
  isPropN-hom = λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → Q.isSetPsh _ _

  isSetPshHom : isSet PshHom
  isSetPshHom = isSetΣ (isSetΠ (λ _ → isSet→ Q.isSetPsh)) λ _ → isProp→isSet (isPropN-hom _)

module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}{Q : Presheaf C ℓS'} where
  makePshHomPath : ∀ {α β : PshHom P Q} → α .fst ≡ β .fst
   → α ≡ β
  makePshHomPath = ΣPathPProp (isPropN-hom P Q)

