-- Free category generated from base objects and generators
-- This time not using a graph as the presentation of the generators
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Free.Category.Quiver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Preorder as Preorder hiding (Section)

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ : Level

open Category
open Functor

record Quiver ℓg ℓg' : Type (ℓ-suc (ℓ-max ℓg ℓg')) where
  field
    ob : Type ℓg
    mor : Type ℓg'
    dom : mor → ob
    cod : mor → ob

open Quiver
module _ (Q : Quiver ℓg ℓg') where
  data Exp : Q .ob → Q .ob → Type (ℓ-max ℓg ℓg') where
    ↑_   : ∀ g → Exp (Q .dom g) (Q .cod g)
    idₑ  : ∀ {A} → Exp A A
    _⋆ₑ_ : ∀ {A B C} → (e : Exp A B) → (e' : Exp B C) → Exp A C
    ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
    ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
    ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
            → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
    isSetExp : ∀ {A B} → isSet (Exp A B)

  FreeCat : Category _ _
  FreeCat .ob = Q .ob
  FreeCat .Hom[_,_] = Exp
  FreeCat .id = idₑ
  FreeCat ._⋆_ = _⋆ₑ_
  FreeCat .⋆IdL = ⋆ₑIdL
  FreeCat .⋆IdR = ⋆ₑIdR
  FreeCat .⋆Assoc = ⋆ₑAssoc
  FreeCat .isSetHom = isSetExp

  -- A displayed interpretation
  open Categoryᴰ
  record Interpᴰ (𝓓 : Categoryᴰ FreeCat ℓd ℓd')
    : Type ((ℓ-max (ℓ-max ℓg ℓg') (ℓ-max ℓd ℓd'))) where
    field
      I-ob : (c : Q .ob) → ob[_] 𝓓 c
      I-hom : ∀ e → 𝓓 [ ↑ e ][ I-ob (Q .dom e) , I-ob (Q .cod e) ]
  open Interpᴰ

  module _ {𝓓 : Categoryᴰ FreeCat ℓd ℓd'} (ı : Interpᴰ 𝓓) where
    open Section

    private
      module 𝓓 = Categoryᴰ 𝓓

    elimF : ∀ {c c'} (f : FreeCat [ c , c' ])
          → 𝓓 [ f ][ ı .I-ob c , ı .I-ob c' ]
    elimF (↑ e) = ı .I-hom e
    elimF idₑ = 𝓓 .idᴰ
    elimF (f ⋆ₑ g) = elimF f 𝓓.⋆ᴰ elimF g
    elimF (⋆ₑIdL f i) = 𝓓 .⋆IdLᴰ (elimF f) i
    elimF (⋆ₑIdR f i) = 𝓓 .⋆IdRᴰ (elimF f) i
    elimF (⋆ₑAssoc f f₁ f₂ i) = 𝓓 .⋆Assocᴰ (elimF f) (elimF f₁) (elimF f₂) i
    elimF (isSetExp f g p q i j) =
      isOfHLevel→isOfHLevelDep 2 (λ x → 𝓓 .isSetHomᴰ)
      (elimF f)
      (elimF g)
      (cong elimF p)
      (cong elimF q)
      (isSetExp f g p q)
      i
      j

    elim : Section 𝓓
    elim .F-ob = ı .I-ob
    elim .F-hom = elimF
    elim .F-id = refl
    elim .F-seq f g = refl

  -- Trivially displayed version of Interpᴰ
  Interp : (𝓒 : Category ℓc ℓc') → Type (ℓ-max (ℓ-max (ℓ-max ℓg ℓg') ℓc) ℓc')
  Interp 𝓒 = Interpᴰ (weaken FreeCat 𝓒)

  η : Interp FreeCat
  η .I-ob = λ c → c
  η .I-hom = ↑_

  rec : {𝓒 : Category ℓc ℓc'} → Interp 𝓒 → Functor FreeCat 𝓒
  rec ı = Iso.fun (SectionToWkIsoFunctor _ _) (elim ı)

  module _ {ℓc ℓc'} {𝓒 : Category ℓc ℓc'} (F G : Functor FreeCat 𝓒)
           (agree-on-gen :
             Interpᴰ (Preorderᴰ→Catᴰ
                     (SecPath (weaken FreeCat 𝓒)
                     (Iso.inv (SectionToWkIsoFunctor _ _) F)
                     (Iso.inv (SectionToWkIsoFunctor _ _) G))))
         where
    FreeCatFunctor≡ : F ≡ G
    FreeCatFunctor≡ = isoInvInjective (SectionToWkIsoFunctor _ _) F G
      (SecPathSectionToSectionPath (weaken FreeCat 𝓒)
      (Iso.inv (PreorderSectionIsoCatSection _ _)
      (elim agree-on-gen)))
