-- Free category generated from base objects and generators
-- This time not using a graph as the presentation of the generators
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Free.Category.Quiver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Quiver.Base as Quiver

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Constructions.Weaken
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.UnderlyingGraph hiding (Interp)

open import Cubical.Categories.Displayed.Section as Cat
open import Cubical.Categories.Displayed.Preorder as Preorder hiding (Section)

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ : Level

open Category
open Functor
open QuiverOver

module _ (Q : Quiver ℓg ℓg') where
  data Exp : Q .fst → Q .fst → Type (ℓ-max ℓg ℓg') where
    ↑_   : ∀ g → Exp (Q .snd .dom g) (Q .snd .cod g)
    idₑ  : ∀ {A} → Exp A A
    _⋆ₑ_ : ∀ {A B C} → (e : Exp A B) → (e' : Exp B C) → Exp A C
    ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
    ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
    ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
            → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
    isSetExp : ∀ {A B} → isSet (Exp A B)

  FreeCat : Category _ _
  FreeCat .ob = Q .fst
  FreeCat .Hom[_,_] = Exp
  FreeCat .id = idₑ
  FreeCat ._⋆_ = _⋆ₑ_
  FreeCat .⋆IdL = ⋆ₑIdL
  FreeCat .⋆IdR = ⋆ₑIdR
  FreeCat .⋆Assoc = ⋆ₑAssoc
  FreeCat .isSetHom = isSetExp

  Interp : (𝓒 : Category ℓc ℓc') → Type (ℓ-max (ℓ-max (ℓ-max ℓg ℓg') ℓc) ℓc')
  Interp 𝓒 = HetQG Q (Cat→Graph 𝓒)

  η : Interp FreeCat
  η HetQG.$g x = x
  η HetQG.<$g> e = ↑ e

  module _ (𝓓 : Categoryᴰ FreeCat ℓd ℓd') where
    Interpᴰ : Type _
    Interpᴰ = Quiver.Section (Quiver.reindex η (Categoryᴰ→Graphᴰ 𝓓))

  module _ {𝓓 : Categoryᴰ FreeCat ℓd ℓd'} (ı : Interpᴰ 𝓓) where
    private
      module ı = Quiver.Section ı
      module 𝓓 = Categoryᴰ 𝓓

    elimF : ∀ {c c'} (f : FreeCat [ c , c' ])
          → 𝓓 [ f ][ ı.F-ob c , ı.F-ob c' ]
    elimF (↑ e) = ı.F-hom e
    elimF idₑ = 𝓓.idᴰ
    elimF (f ⋆ₑ g) = elimF f 𝓓.⋆ᴰ elimF g
    elimF (⋆ₑIdL f i) = 𝓓.⋆IdLᴰ (elimF f) i
    elimF (⋆ₑIdR f i) = 𝓓.⋆IdRᴰ (elimF f) i
    elimF (⋆ₑAssoc f f₁ f₂ i) = 𝓓.⋆Assocᴰ (elimF f) (elimF f₁) (elimF f₂) i
    elimF (isSetExp f g p q i j) =
      isOfHLevel→isOfHLevelDep 2 (λ x → 𝓓.isSetHomᴰ)
      (elimF f)
      (elimF g)
      (cong elimF p)
      (cong elimF q)
      (isSetExp f g p q)
      i
      j

    open Cat.Section
    elim : Cat.Section 𝓓
    elim .F-ob = ı.F-ob
    elim .F-hom = elimF
    elim .F-id = refl
    elim .F-seq f g = refl

  module _ {ℓc ℓc'} {𝓒 : Categoryᴰ FreeCat ℓc ℓc'} (F G : Cat.Section 𝓒)
    (agree-on-gen : Interpᴰ (Preorderᴰ→Catᴰ (SecPath _ F G))) where
    FreeCatSection≡ : F ≡ G
    FreeCatSection≡ =
      SecPathSectionToSectionPath
        _
        (Iso.inv (PreorderSectionIsoCatSection _ _) (elim agree-on-gen))

  module _ {𝓒 : Category ℓc ℓc'} (ı : Interp 𝓒) where
    private
      open HetQG
      ıᴰ : Interpᴰ (weaken FreeCat 𝓒)
      ıᴰ .Section.F-ob q  = ı $g q
      ıᴰ .Section.F-hom e = ı <$g> e

    rec : Functor FreeCat 𝓒
    rec = Iso.fun (SectionToWkIsoFunctor _ _) (elim ıᴰ)

  module _ {ℓc ℓc'} {𝓒 : Category ℓc ℓc'} (F G : Functor FreeCat 𝓒)
           (agree-on-gen :
             Interpᴰ (Preorderᴰ→Catᴰ
                     (SecPath (weaken FreeCat 𝓒)
                     (Iso.inv (SectionToWkIsoFunctor _ _) F)
                     (Iso.inv (SectionToWkIsoFunctor _ _) G))))
         where
    FreeCatFunctor≡ : F ≡ G
    FreeCatFunctor≡ =
      isoInvInjective (SectionToWkIsoFunctor _ _) F G
                      (FreeCatSection≡ _ _ agree-on-gen)
