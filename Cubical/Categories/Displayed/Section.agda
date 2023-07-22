{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Section where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More

open import Cubical.Categories.Displayed.Preorder as Preorder hiding (Section)

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Categoryᴰ
open Functor

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where
  private
    module D = Categoryᴰ D

  record Section : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    field
      F-ob : ∀ c → D.ob[ c ]
      F-hom : ∀ {c c'} (f : C [ c , c' ]) → D [ f ][ F-ob c , F-ob c' ]
      F-id : ∀ {c} → F-hom (C .id {c}) ≡ D .idᴰ
      F-seq : ∀ {c c' c''} (f : C [ c , c' ])(g : C [ c' , c'' ])
            → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) D.⋆ᴰ (F-hom g)

  open Section
  Section≡ : {F G : Section}
           → (h : ∀ c → F .F-ob c ≡ G .F-ob c)
           → (∀ {c c'} (f : C [ c , c' ])
           → PathP (λ i → D [ f ][ h c i , h c' i ]) (F .F-hom f) (G .F-hom f))
           → F ≡ G
  Section≡ hOb hHom i .F-ob c = hOb c i
  Section≡ hOb hHom i .F-hom f = hHom f i
  Section≡ {F = F}{G = G} hOb hHom i .F-id =
    isProp→PathP (λ j → D .isSetHomᴰ (hHom (C .id) j) (D .idᴰ))
    (F .F-id)
    (G .F-id)
    i
  Section≡ {F = F}{G = G} hOb hHom i .F-seq f g =
    isProp→PathP
      (λ j → D .isSetHomᴰ (hHom (f ⋆⟨ C ⟩ g) j) (hHom f j D.⋆ᴰ hHom g j))
      (F .F-seq f g)
      (G .F-seq f g)
      i

  SectionToFunctor : Section → Functor C (∫C D)
  SectionToFunctor F .F-ob x = x , F .F-ob x
  SectionToFunctor F .F-hom f = f , (F .F-hom f)
  SectionToFunctor F .F-id = ΣPathP (refl , (F .F-id))
  SectionToFunctor F .F-seq f g = ΣPathP (refl , (F .F-seq f g))

  SectionIsSection : ∀ (F : Section) → (Fst {Cᴰ = D} ∘F SectionToFunctor F) ≡ Id
  SectionIsSection F = Functor≡ (λ c → refl) λ f → refl

  open Preorderᴰ
  SecPath : (F G : Section) → Preorderᴰ C ℓD ℓD'
  SecPath F G .ob[_] c = Path (D.ob[ c ]) (F .F-ob c) (G .F-ob c)
  SecPath F G .Hom[_][_,_] f p q =
    PathP (λ i → D [ f ][ p i , q i ])
          (F .F-hom f)
          (G .F-hom f)
  SecPath F G .idᴰ = F .F-id ◁ (λ i → D .idᴰ) ▷ sym (G .F-id)
  SecPath F G ._⋆ᴰ_ p q =
    F .F-seq _ _ ◁ (λ i → p i D.⋆ᴰ q i) ▷ sym (G .F-seq _ _)
  SecPath F G .isPropHomᴰ = isOfHLevelPathP' 1 (D .isSetHomᴰ) _ _

  open Section
  open Preorder.Section

  SecPathSectionToSectionPath : {F G : Section}
                              → Preorder.Section (SecPath F G)
                              → F ≡ G
  SecPathSectionToSectionPath p = Section≡
    (λ c → p .F-ob c)
    λ f → p .F-hom f

open Section
open Preorder.Section
module _ (C : Category ℓC ℓC') (P : Preorderᴰ C ℓD ℓD') where
  open Iso
  open Preorderᴰ
  PreorderSectionIsoCatSection
    : Iso (Preorder.Section P) (Section (Preorderᴰ→Catᴰ P))
  PreorderSectionIsoCatSection .fun F .F-ob = F .F-ob
  PreorderSectionIsoCatSection .fun F .F-hom = F .F-hom
  PreorderSectionIsoCatSection .fun F .F-id = P .isPropHomᴰ _ _
  PreorderSectionIsoCatSection .fun F .F-seq f g = P .isPropHomᴰ _ _
  PreorderSectionIsoCatSection .inv F .F-ob = F .F-ob
  PreorderSectionIsoCatSection .inv F .F-hom = F .F-hom
  PreorderSectionIsoCatSection .rightInv b =
    Section≡ _ (λ c → refl) (λ f → refl)
  PreorderSectionIsoCatSection .leftInv a = refl

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  weaken : Categoryᴰ C ℓD ℓD'
  weaken .ob[_] x = D .ob
  weaken .Hom[_][_,_] f d d' = D [ d , d' ]
  weaken .idᴰ = D .id
  weaken ._⋆ᴰ_ = D ._⋆_
  weaken .⋆IdLᴰ = D .⋆IdL
  weaken .⋆IdRᴰ = D .⋆IdR
  weaken .⋆Assocᴰ = D .⋆Assoc
  weaken .isSetHomᴰ = D .isSetHom

  open Iso
  SectionToWkIsoFunctor : Iso (Section weaken) (Functor C D)
  SectionToWkIsoFunctor .fun F .F-ob = F .F-ob
  SectionToWkIsoFunctor .fun F .F-hom = F .F-hom
  SectionToWkIsoFunctor .fun F .F-id = F .F-id
  SectionToWkIsoFunctor .fun F .F-seq = F .F-seq
  SectionToWkIsoFunctor .inv F .F-ob = F .F-ob
  SectionToWkIsoFunctor .inv F .F-hom = F .F-hom
  SectionToWkIsoFunctor .inv F .F-id = F .F-id
  SectionToWkIsoFunctor .inv F .F-seq = F .F-seq
  SectionToWkIsoFunctor .rightInv b = Functor≡ (λ _ → refl) (λ _ → refl)
  SectionToWkIsoFunctor .leftInv a = refl
