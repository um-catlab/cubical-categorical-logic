-- TODO: re-org this and upstream it
module Cubical.Categories.Presheaf.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable


open Functor
open Iso
open NatIso
open NatTrans

private
  variable
    ℓ ℓ' ℓP ℓQ ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' : Level

𝓟o = Presheaf

𝓟* : Category ℓ ℓ' → (ℓS : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
𝓟* C ℓS = Functor C (SET ℓS)

module _ (C : Category ℓ ℓ') (c : C .Category.ob) where
  open Category
  open UniversalElement
  -- This is a great argument against using universal elements(!)
  selfUnivElt :  UniversalElement C (C [-, c ])
  selfUnivElt .vertex = c
  selfUnivElt .element = C .id
  selfUnivElt .universal A = isoToIsEquiv (iso _ (λ z → z)
    (C .⋆IdR)
    (C .⋆IdR))

module _ {ℓo}{ℓh}{ℓp} (C : Category ℓo ℓh) (P : Presheaf C ℓp) where
  open Category
  open UniversalElement
  UniversalElementOn : C .ob → Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  UniversalElementOn vertex =
    Σ[ element ∈ (P ⟅ vertex ⟆) .fst ] isUniversal C P vertex element

  UniversalElementToUniversalElementOn :
    (ue : UniversalElement C P) → UniversalElementOn (ue .vertex)
  UniversalElementToUniversalElementOn ue .fst = ue .element
  UniversalElementToUniversalElementOn ue .snd = ue .universal

module PresheafNotation {ℓo}{ℓh}
       {C : Category ℓo ℓh} {ℓp} (P : Presheaf C ℓp)
       where
  private
    module C = Category C
  p[_] : C.ob → Type ℓp
  p[ x ] = ⟨ P ⟅ x ⟆ ⟩

  infixr 9 _⋆_
  _⋆_ : ∀ {x y} (f : C [ x , y ]) (g : p[ y ]) → p[ x ]
  f ⋆ g = P .F-hom f g

  ⋆IdL : ∀ {x} (g : p[ x ]) → C.id ⋆ g ≡ g
  ⋆IdL = funExt⁻ (P .F-id)

  ⋆Assoc : ∀ {x y z} (f : C [ x , y ])(g : C [ y , z ])(h : p[ z ]) →
    (f C.⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
  ⋆Assoc f g = funExt⁻ (P .F-seq g f)

  ⟨_⟩⋆⟨_⟩ : ∀ {x y} {f f' : C [ x , y ]} {g g' : p[ y ]}
            → f ≡ f' → g ≡ g' → f ⋆ g ≡ f' ⋆ g'
  ⟨ f≡f' ⟩⋆⟨ g≡g' ⟩ = cong₂ _⋆_ f≡f' g≡g'

  ⟨⟩⋆⟨_⟩ : ∀ {x y} {f : C [ x , y ]} {g g' : p[ y ]}
            → g ≡ g' → f ⋆ g ≡ f ⋆ g'
  ⟨⟩⋆⟨_⟩ = ⟨ refl ⟩⋆⟨_⟩

  ⟨_⟩⋆⟨⟩ : ∀ {x y} {f f' : C [ x , y ]} {g : p[ y ]}
            → f ≡ f' → f ⋆ g ≡ f' ⋆ g
  ⟨_⟩⋆⟨⟩ = ⟨_⟩⋆⟨ refl ⟩

  isSetPsh : ∀ {x} → isSet (p[ x ])
  isSetPsh {x} = (P ⟅ x ⟆) .snd
