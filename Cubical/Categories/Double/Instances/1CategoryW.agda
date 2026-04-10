{-# OPTIONS --lossy-unification #-}
-- Test instance of DoubleCategoryW: turn a 1-category into a double
-- category using its hom as horizontal arrows and cubical paths for
-- verticals.  Adapted from 1Cat→DoubleCatᴴ in
-- Cubical.Categories.Double.Instances.1Category.
--
-- This exists primarily to verify that the naturality axioms of
-- DoubleCategoryW can be inhabited as plain equations, without any
-- PathP gymnastics over `⋆ⱽIdR v ∙ sym (⋆ⱽIdL v)`.
module Cubical.Categories.Double.Instances.1CategoryW where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Double.BaseW

open DoubleCategoryW

module _ {ℓ ℓ'} (C : Category ℓ ℓ') where
  private
    module C = Category C

  -- Category structure of C encoded with horizontal morphisms, only
  -- identity vertical morphisms and squares.  Same shape as
  -- 1Cat→DoubleCatᴴ, but inhabiting the whiskered record.
  1Cat→DoubleCatWᴴ : DoubleCategoryW _ _ _ _
  1Cat→DoubleCatWᴴ .ob = C.ob
  1Cat→DoubleCatWᴴ .Homⱽ[_,_] = _≡_
  1Cat→DoubleCatWᴴ .idⱽ = refl
  1Cat→DoubleCatWᴴ ._⋆ⱽ_ = _∙_
  1Cat→DoubleCatWᴴ .⋆ⱽIdL f = sym $ lUnit f
  1Cat→DoubleCatWᴴ .⋆ⱽIdR f = sym $ rUnit f
  1Cat→DoubleCatWᴴ .⋆ⱽAssoc f g h = sym $ assoc f g h
  1Cat→DoubleCatWᴴ .Homᴴ[_,_] = C.Hom[_,_]
  1Cat→DoubleCatWᴴ .idᴴ = C.id
  1Cat→DoubleCatWᴴ ._⋆ᴴ_ = C._⋆_
  1Cat→DoubleCatWᴴ .Sq f g e e' = PathP (λ i → C [ e i , e' i ]) f g
  1Cat→DoubleCatWᴴ .isSetSq = isProp→isSet (isOfHLevelPathP' 1 C.isSetHom _ _)
  1Cat→DoubleCatWᴴ .idⱽSq = refl
  1Cat→DoubleCatWᴴ .idᴴSq {v = p} i = C.id
  1Cat→DoubleCatWᴴ ._⋆ⱽSq_ {←f = ←f} {→f = →f} {←f' = ←f'} {→f' = →f'} α β i =
    comp (λ j → C [ compPath-filler ←f ←f' j i , compPath-filler →f →f' j i ])
         (λ j → λ { (i = i0) → α i0 ; (i = i1) → β j })
         (α i)
  1Cat→DoubleCatWᴴ .⋆ⱽIdLSq _ =
    isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatWᴴ .⋆ⱽIdRSq _ =
    isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatWᴴ .⋆ⱽAssocSq _ _ _ =
    isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatWᴴ ._⋆ᴴSq_ α β i = α i C.⋆ β i

  -- Whiskering: the vertical side of Sq is a PathP over C.Hom; ◃/▹
  -- extend its right/left endpoint along a globular cell (a path in
  -- C.Hom) via hcomp.  ⊙ⱽ is plain path composition since both sides
  -- live in a fixed hom-set.
  1Cat→DoubleCatWᴴ ._◃_ α β i =
    hcomp (λ j → λ { (i = i0) → α i0
                   ; (i = i1) → β j })
          (α i)
  1Cat→DoubleCatWᴴ ._▹_ α β i =
    hcomp (λ j → λ { (i = i0) → α (~ j)
                   ; (i = i1) → β i1 })
          (β i)
  1Cat→DoubleCatWᴴ ._⊙ⱽ_ α β = α ∙ β

  -- All coherences between whiskering and ⋆ⱽSq are squares in the set
  -- C.Hom, filled automatically.
  1Cat→DoubleCatWᴴ .◃≡⋆ⱽSq _ _ =
    isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatWᴴ .▹≡⋆ⱽSq _ _ =
    isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatWᴴ .⊙ⱽ≡⋆ⱽSq _ _ =
    isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _

  1Cat→DoubleCatWᴴ .λᴴ = C.⋆IdL
  1Cat→DoubleCatWᴴ .λᴴ⁻ f = sym (C.⋆IdL f)
  -- Isomorphism and naturality axioms: equalities between squares,
  -- which unfold to 2-dimensional fillings in C.Hom (a set).
  1Cat→DoubleCatWᴴ .λᴴλᴴ⁻ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatWᴴ .λᴴ⁻λᴴ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  -- Naturality: plain equation between squares, no composite base.
  1Cat→DoubleCatWᴴ .λᴴ-nat _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _

  1Cat→DoubleCatWᴴ .ρᴴ = C.⋆IdR
  1Cat→DoubleCatWᴴ .ρᴴ⁻ f = sym (C.⋆IdR f)
  1Cat→DoubleCatWᴴ .ρᴴρᴴ⁻ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatWᴴ .ρᴴ⁻ρᴴ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatWᴴ .ρᴴ-nat _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _

  1Cat→DoubleCatWᴴ .αᴴ = C.⋆Assoc
  1Cat→DoubleCatWᴴ .αᴴ⁻ f g h = sym (C.⋆Assoc f g h)
  1Cat→DoubleCatWᴴ .αᴴαᴴ⁻ _ _ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatWᴴ .αᴴ⁻αᴴ _ _ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  -- αᴴ-nat: the key one.  Plain equation, no composite base path.
  1Cat→DoubleCatWᴴ .αᴴ-nat _ _ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _

  1Cat→DoubleCatWᴴ .pentagon _ _ _ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatWᴴ .triangle _ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatWᴴ .interchange _ _ _ _ =
    isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
