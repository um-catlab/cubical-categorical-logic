{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Sets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Displayed.Instances.Functor
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓC ℓC' ℓD ℓD' : Level

module _ ℓ ℓ' where
  open Categoryᴰ
  SETᴰ : Categoryᴰ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  SETᴰ .ob[_] X = ⟨ X ⟩ → hSet ℓ'
  SETᴰ .Hom[_][_,_] f P Q = ∀ x → ⟨ P x ⟩ → ⟨ Q (f x) ⟩
  SETᴰ .idᴰ = λ x z → z
  SETᴰ ._⋆ᴰ_ {f = f} {g} fᴰ gᴰ x p = gᴰ (f x) (fᴰ x p)
  SETᴰ .⋆IdLᴰ fᴰ = refl
  SETᴰ .⋆IdRᴰ fᴰ = refl
  SETᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = refl
  SETᴰ .isSetHomᴰ {yᴰ = Q} = isSetΠ λ x → isSetΠ λ xᴰ → Q _ .snd

open Category
open Functorᴰ
-- Displayed representable
_[-][-,_] : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → {c : C .ob}
          → Categoryᴰ.ob[_] D c
          → Functorᴰ (C [-, c ]) (D ^opᴰ) (SETᴰ ℓC' ℓD')
_[-][-,_] {C = C} D {c} d .F-obᴰ d' f =
  (D [ f ][ d' , d ]) , Categoryᴰ.isSetHomᴰ D
_[-][-,_] {C = C} D {c} d .F-homᴰ fᴰ g gᴰ = Categoryᴰ._⋆ᴰ_ D fᴰ gᴰ
_[-][-,_] {C = C} D {c} d .F-idᴰ i g gᴰ = Categoryᴰ.⋆IdLᴰ D gᴰ i
_[-][-,_] {C = C} D {c} d .F-seqᴰ fᴰ gᴰ i h hᴰ = Categoryᴰ.⋆Assocᴰ D gᴰ fᴰ hᴰ i

module _ {C : Category ℓ ℓ'}{Cᴰ : Categoryᴰ C ℓ'' ℓ'''} where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  open NatTransᴰ
  YOᴰ : Functorᴰ (YO {C = C}) Cᴰ (FUNCTORᴰ (Cᴰ ^opᴰ) (SETᴰ ℓ' ℓ'''))
  YOᴰ .F-obᴰ xᴰ = Cᴰ [-][-, xᴰ ]
  YOᴰ .F-homᴰ fᴰ .N-obᴰ xᴰ g gᴰ = gᴰ Cᴰ.⋆ᴰ fᴰ
  YOᴰ .F-homᴰ fᴰ .N-homᴰ gᴰ i h hᴰ = Cᴰ.⋆Assocᴰ gᴰ hᴰ fᴰ i
  YOᴰ .F-idᴰ = makeNatTransPathᴰ (Cᴰ ^opᴰ) (SETᴰ ℓ' ℓ''') _ λ i xᴰ f fᴰ →
    Cᴰ.⋆IdRᴰ fᴰ i
  YOᴰ .F-seqᴰ fᴰ gᴰ = makeNatTransPathᴰ _ _ _ (λ i xᴰ f hᴰ →
    Cᴰ.⋆Assocᴰ hᴰ fᴰ gᴰ (~ i))

-- Displayed representable
_[-][_,-] : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → {c : C .ob}
          → Categoryᴰ.ob[_] D c
          → Functorᴰ (C [ c ,-]) D (SETᴰ ℓC' ℓD')
(D [-][ d ,-]) .F-obᴰ d' f = (D [ f ][ d , d' ]) , Categoryᴰ.isSetHomᴰ D
(D [-][ d ,-]) .F-homᴰ fᴰ g gᴰ = Categoryᴰ._⋆ᴰ_ D gᴰ fᴰ
(D [-][ d ,-]) .F-idᴰ i f fᴰ = Categoryᴰ.⋆IdRᴰ D fᴰ i
(D [-][ d ,-]) .F-seqᴰ fᴰ gᴰ i h hᴰ = Categoryᴰ.⋆Assocᴰ D hᴰ fᴰ gᴰ (~ i)

open Functor
ΣF : Functor (∫C (SETᴰ ℓ ℓ')) (SET (ℓ-max ℓ ℓ'))
ΣF .F-ob (A , B) .fst = Σ[ a ∈ ⟨ A ⟩ ] ⟨ B a ⟩
ΣF .F-ob (A , B) .snd = isSetΣ (A .snd) (λ a → B a .snd)
ΣF .F-hom (f , g) (x , y) = (f x) , (g x y)
ΣF .F-id = refl
ΣF .F-seq f g = refl

×Setsᴰ : Functorᴰ ×Sets
  (SETᴰ ℓ ℓ' ×Cᴰ SETᴰ ℓ'' ℓ''')
  (SETᴰ (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ'''))
×Setsᴰ .F-obᴰ (B₁ , B₂) (a₁ , a₂) =
  (⟨ B₁ a₁ ⟩ × ⟨ B₂ a₂ ⟩)
  , (isSet× (B₁ a₁ .snd) (B₂ a₂ .snd))
×Setsᴰ .F-homᴰ (g₁ , g₂) (a₁ , a₂) (b₁ , b₂) = g₁ a₁ b₁ , g₂ a₂ b₂
×Setsᴰ .F-idᴰ = refl
×Setsᴰ .F-seqᴰ fᴰ gᴰ = refl
