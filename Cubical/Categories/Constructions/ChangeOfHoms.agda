{-

  Given a category C and a family of type f : C .ob → C.ob → Type _
  such that f a b ≅ Hom a b, make a new category
  whose morphisms are given by f

  This is useful for cleaning up compositional constructions that end
  up with useless data in the homs like Hom a b × 1.

-}
module Cubical.Categories.Constructions.ChangeOfHoms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism

-- open import Cubical.Functions.Embedding

-- open import Cubical.Data.Sigma

-- open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
-- open import Cubical.Categories.Constructions.FullSubcategory

private
  variable
    ℓC ℓC' ℓD ℓD' ℓX : Level


open Category
open Functor
open Iso

module _
  (C : Category ℓC ℓC')
  (F : (C .ob) → (C .ob) → Type ℓX)
  (F-iso : ∀ (c d : C .ob) → Iso (C [ c , d ]) (F c d))
  where

  private
    module C = Category C
    module _ {c}{d} where
      Ffun = F-iso c d .fun
      Finv = F-iso c d .inv
      Fsec = F-iso c d .leftInv
      Fret = F-iso c d .rightInv

  ChangeOfHoms : Category ℓC ℓX
  ChangeOfHoms .ob = C .ob
  ChangeOfHoms .Hom[_,_] = F
  ChangeOfHoms .id = Ffun (C .id)
  ChangeOfHoms ._⋆_ f g = Ffun (Finv f C.⋆ Finv g)
  ChangeOfHoms .⋆IdL f =
    cong Ffun (cong₂ C._⋆_ (Fsec C.id) refl ∙ C.⋆IdL _) ∙ Fret f
  ChangeOfHoms .⋆IdR f =
    cong Ffun (cong₂ C._⋆_ refl (Fsec C.id) ∙ C.⋆IdR _) ∙ Fret f
  ChangeOfHoms .⋆Assoc f g h =
    cong Ffun
      (cong₂ C._⋆_ (Fsec (Finv f C.⋆ Finv g)) refl
      ∙ C.⋆Assoc _ _ _
      ∙ cong₂ C._⋆_ refl (sym (Fsec (Finv g C.⋆ Finv h))))
  ChangeOfHoms .isSetHom = isSetRetract Finv Ffun Fret (C .isSetHom)

  π : Functor ChangeOfHoms C
  π .F-ob = λ z → z
  π .F-hom = Finv
  π .F-id =
    leftInv (F-iso (π .F-ob _) (π .F-ob _)) C.id
  π .F-seq _ _ =
    leftInv (F-iso (π .F-ob _) (π .F-ob _)) (Finv _ C.⋆ Finv _)
