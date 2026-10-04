open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched

-- Enrichment, following "Univalent Enriched Categories and the Enriched Rezk Completion" (v.d. Weide 2026)
-- Notation for homset bijection taken from "First steps …" (Birkedal et al 2012)
module Cubical.Categories.Enriched.Enrichment.Base
  {ℓV ℓV' ℓC ℓC' : Level}
  (C : Category ℓC ℓC')
  (V : MonoidalCategory ℓV ℓV') where

open import Cubical.Foundations.Isomorphism

open MonoidalCategory V
  renaming (ob to obV; Hom[_,_] to V[_,_]; id to idV; _⋆_ to _⋆V_) hiding (C)

open Category C using (Hom[_,_];ob)

record Enrichment : Type (ℓ-max (ℓ-max ℓV ℓV') (ℓ-max ℓC ℓC')) where
   field
      VE[_,_] : ob → ob → obV
      id : ∀ {x} → V[ unit , VE[ x , x ] ]
      seq : ∀ x y z → V[ VE[ x , y ] ⊗ VE[ y , z ] , VE[ x , z ] ]
      ⇄-agree : ∀ {x y} → Iso Hom[ x , y ] V[ unit , VE[ x , y ] ]
      ⋆IdL : ∀ x y →   η⟨ _ ⟩  ≡  (id {x} ⊗ₕ idV)  ⋆V  (seq x x y)
      ⋆IdR : ∀ x y →   ρ⟨ _ ⟩  ≡  (idV ⊗ₕ id {y})  ⋆V  (seq x y y)
      ⋆Assoc : ∀ x y z w →
          α⟨ _ , _ , _ ⟩  ⋆V  ((seq x y z) ⊗ₕ idV)  ⋆V  (seq x z w)
                          ≡  (idV ⊗ₕ (seq y z w))  ⋆V  (seq x y w)
      ⌜id⌝ : ∀ {x} →
          Iso.fun (⇄-agree {x} {x}) (Category.id C) ≡ id {x}
      ⌜⋆⌝ : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ]) →
          Iso.fun (⇄-agree {x} {z}) ((C Category.⋆ f) g)
          ≡ η⁻¹⟨ _ ⟩ ⋆V (Iso.fun ⇄-agree f ⊗ₕ Iso.fun ⇄-agree g) ⋆V seq x y z

   module _ {x y : ob} where
     open Iso (⇄-agree {x = x} {y = y})

     ⌜_⌝ : Hom[ x , y ] → V[ unit , VE[ x , y ] ]
     ⌜_⌝ = fun
     ⌞_⌟ : V[ unit , VE[ x , y ] ] → Hom[ x , y ]
     ⌞_⌟ = inv
     ⇄-agree→ : ∀ (f : Hom[ x , y ]) → ⌞ ⌜ f ⌝ ⌟ ≡ f
     ⇄-agree→ = ret
     ⇄-agree← : ∀ (f : V[ unit , VE[ x , y ] ]) → ⌜ ⌞ f ⌟ ⌝ ≡ f
     ⇄-agree← = sec

-- Forget the plain-category structure (and `⇄-agree`) to get the
-- underlying V-enriched category.
toEnrichedCategory : Enrichment → EnrichedCategory V ℓC
toEnrichedCategory E = record
  { ob       = Category.ob C
  ; Hom[_,_] = E.VE[_,_]
  ; id       = E.id
  ; seq      = E.seq
  ; ⋆IdL     = E.⋆IdL
  ; ⋆IdR     = E.⋆IdR
  ; ⋆Assoc   = E.⋆Assoc
  } where module E = Enrichment E
