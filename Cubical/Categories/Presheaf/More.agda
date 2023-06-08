{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.More where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Presheaf.Base

open import Cubical.Categories.Instances.Sets.More

open Category
open Functor

private
  variable
    ℓ ℓ' ℓS ℓS' : Level

action : ∀ (C : Category ℓ ℓ') → (P : Presheaf C ℓS) → {a b : C .ob} →
         C [ a , b ] → fst (P ⟅ b ⟆) → fst (P ⟅ a ⟆)
action C P = P .F-hom

-- Convenient notation for naturality
syntax action C P f ϕ = C [ ϕ ∘ᴾ⟨ P ⟩ f ]

∘ᴾId : ∀ (C : Category ℓ ℓ') → (P : Presheaf C ℓS) → {a : C .ob}
     → (ϕ : fst (P ⟅ a ⟆))
     → C [ ϕ ∘ᴾ⟨ P ⟩ C .id ] ≡ ϕ
∘ᴾId C P ϕ i = P .F-id i ϕ

∘ᴾAssoc : ∀ (C : Category ℓ ℓ') → (P : Presheaf C ℓS) → {a b c : C .ob}
        → (ϕ : fst (P ⟅ c ⟆))
        → (f : C [ b , c ])
        → (g : C [ a , b ])
        → C [ ϕ ∘ᴾ⟨ P ⟩ (f ∘⟨ C ⟩ g) ] ≡ C [ C [ ϕ ∘ᴾ⟨ P ⟩ f ] ∘ᴾ⟨ P ⟩ g ]
∘ᴾAssoc C P ϕ f g i = P .F-seq f g i ϕ

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
