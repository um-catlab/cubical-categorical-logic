{-# OPTIONS --safe #-}

module Cubical.Categories.Displayed.Preorder where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

record Preorderᴰ (C : Category ℓC ℓC') ℓCᴰ ℓCᴰ' :
  Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))) where
  open Category C
  field
    ob[_] : ob → Type ℓCᴰ
    Hom[_][_,_] : {x y : ob} → Hom[ x , y ] → ob[ x ] → ob[ y ] → Type ℓCᴰ'
    idᴰ : ∀ {x} {p : ob[ x ]} → Hom[ id ][ p , p ]
    _⋆ᴰ_ : ∀ {x y z} {f : Hom[ x , y ]} {g : Hom[ y , z ]} {xᴰ yᴰ zᴰ}
      → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f ⋆ g ][ xᴰ , zᴰ ]
    isPropHomᴰ : ∀ {x y} {f : Hom[ x , y ]} {xᴰ yᴰ} → isProp Hom[ f ][ xᴰ , yᴰ ]

module _ {C : Category ℓC ℓC'} (Pᴰ : Preorderᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  open Preorderᴰ
  Preorderᴰ→Catᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
  Preorderᴰ→Catᴰ = record
    { ob[_] = Pᴰ .ob[_]
    ; Hom[_][_,_] = Pᴰ .Hom[_][_,_]
    ; idᴰ = Pᴰ .idᴰ
    ; _⋆ᴰ_ = Pᴰ ._⋆ᴰ_
    ; ⋆IdLᴰ = λ _ →
      isProp→PathP ((λ i → Pᴰ .isPropHomᴰ {f = ((C .⋆IdL _) i)})) _ _
    ; ⋆IdRᴰ = λ _ →
      isProp→PathP ((λ i → Pᴰ .isPropHomᴰ {f = ((C .⋆IdR _) i)})) _ _
    ; ⋆Assocᴰ = λ _ _ _ →
      isProp→PathP ((λ i → Pᴰ .isPropHomᴰ {f = ((C .⋆Assoc _ _ _) i)})) _ _
    ; isSetHomᴰ = isProp→isSet (Pᴰ .isPropHomᴰ)
    }

module _ {C : Category ℓC ℓC'} where
  open Functor

  Fst : {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} → Functor (∫C Cᴰ) C
  Fst .F-ob = fst
  Fst .F-hom = fst
  Fst .F-id = refl
  Fst {Cᴰ = Cᴰ} .F-seq =
    λ f g → cong {x = f ⋆⟨ ∫C Cᴰ ⟩ g} fst refl

  open Preorderᴰ

  Preorderᴰ→FstFaithful : (Pᴰ : Preorderᴰ C ℓCᴰ ℓCᴰ')
    → isFaithful (Fst {Cᴰ = Preorderᴰ→Catᴰ Pᴰ})
  Preorderᴰ→FstFaithful Pᴰ x y f g p =
    ΣPathP (p , isProp→PathP (λ i → Pᴰ .isPropHomᴰ {f = p i}) (f .snd) (g .snd))
