module HyperDoc.Syntax where 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category hiding(isUnivalent)
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Relation.Binary.Preorder


open Category
open Functor
open PreorderStr

private 
  variable 
    ℓ ℓ' ℓP ℓP' : Level
    C : Category ℓ ℓ'
    F : Functor (C ^op) (POSET ℓP ℓP')

module HDSyntax
  {C : Category ℓ ℓ'}
  (F : Functor (C ^op) (POSET ℓP ℓP')) where

  private
    poset = (POSET ℓP ℓP')

  ∣_∣ : ob poset  → Type ℓP
  ∣_∣ p = p .fst .fst
  
  F∣_∣ : ob C → Type ℓP 
  F∣_∣ c = F .F-ob c .fst .fst

  _◂_≤_ : (c : ob C) → F∣ c ∣ → F∣ c ∣ → Type ℓP' 
  _◂_≤_ c p q = F .F-ob c .fst .snd ._≤_ p q

  f* : {c c' : ob C}(f : C [ c , c' ]) → F∣ c' ∣ → F∣ c ∣ 
  f* f = F .F-hom f .MonFun.f

  isProp≤ : {c : ob C}{p q : F∣ c ∣} → isProp (c ◂ p ≤ q) 
  isProp≤  {c}{p}{q} = IsPreorder.is-prop-valued (isPreorder (F .F-ob c .fst .snd)) p q 

  f*id : {c : ob C}{p : F∣ c ∣} → f* (C .id) p ≡ p 
  f*id {c}{p} = cong (λ h → h .MonFun.f p ) (F .F-id)

  f*id' : {c : ob C}{p q : F∣ c ∣} → c ◂ p ≤ q → c ◂ p ≤ f* (C .id) q 
  f*id' {c}{p}{q} t = subst (λ h → c ◂ p ≤ h) (sym f*id) t

  id⊢ : {c : ob C}{p : F∣ c ∣} → c ◂ p ≤ p 
  id⊢ {c}{p} = IsPreorder.is-refl (isPreorder (F .F-ob c .fst .snd)) p

  id' : (c : ob C)(p : F∣ c ∣) → c ◂ p ≤ p 
  id' c p = is-refl (F .F-ob c .fst .snd) p

  eqTo≤ : {c : ob C}{p q : F∣ c ∣}(prf : p ≡ q) → c ◂ p ≤ q 
  eqTo≤ {c} {p}{q}  prf = subst (λ h → c ◂ p ≤ h) prf (id' c p) 

  seq : {c : ob C}{p q r : F∣ c ∣} → c ◂ p ≤  q → c ◂ q ≤ r → c ◂ p ≤ r
  seq {c} f g = IsPreorder.is-trans (isPreorder (F .F-ob c .fst .snd)) _ _ _  f g

  mon* : ∀{x y xᴰ x'ᴰ}(f : C [ y , x ]) → x ◂ xᴰ ≤ x'ᴰ → y ◂ f* f xᴰ ≤ f* f x'ᴰ 
  mon* f = F .F-hom f .MonFun.isMon

  seq* : ∀ {x y z xᴰ yᴰ zᴰ}(f : C [ x , y ])(g : C [ y , z ]) → 
    x ◂ xᴰ ≤ f* f yᴰ → y ◂ yᴰ ≤ f* g zᴰ → x ◂ xᴰ ≤ f* ((C ⋆ f) g) zᴰ 
  seq* {zᴰ = zᴰ} f g p q = seq (seq p (mon* f q)) (eqTo≤ λ i → sym (F .F-seq g f) i .MonFun.f zᴰ)
