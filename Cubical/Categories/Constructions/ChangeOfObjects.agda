{-

  Given a category C and a function X → C .ob, make a new category
  whose objects are X and morphisms are given by C.

  This is useful for cleaning up compositional constructions that end
  up with useless data in the objects like X × 1.

-}
module Cubical.Categories.Constructions.ChangeOfObjects where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.FullSubcategory

private
  variable
    ℓC ℓC' ℓD ℓD' ℓX : Level


open Category
open Functor

module _
  {X : Type ℓX}
  (C : Category ℓC ℓC')
  (F : X → (C .ob)) where

  -- This can't be defined as the FullImage of a functor out of the
  -- discrete category unless X is a hGroupoid
  ChangeOfObjects : Category ℓX ℓC'
  ChangeOfObjects .ob = X
  ChangeOfObjects .Hom[_,_] x y = C [ F x , F y ]
  ChangeOfObjects .id = C .id
  ChangeOfObjects ._⋆_ = C ._⋆_
  ChangeOfObjects .⋆IdL = C .⋆IdL
  ChangeOfObjects .⋆IdR = C .⋆IdR
  ChangeOfObjects .⋆Assoc = C .⋆Assoc
  ChangeOfObjects .isSetHom = C .isSetHom

  π : Functor ChangeOfObjects C
  π .F-ob = F
  π .F-hom = λ z → z
  π .F-id = refl
  π .F-seq _ _ = refl

  -- the following is the right corecursion principle but I didn't
  -- bother to finish it bc transport and I haven't needed it yet.
  -- If GF in this case is refl, it's easier to η expand anyway.
  -- corec : ∀ {D : Category ℓD ℓD'}
  --   → (G : Functor D C)
  --   → (Go : D .ob → X)
  --   → (G .F-ob ≡ λ d → F (Go d))
  --   → Functor D ChangeOfObjects
  -- corec G Go GF .F-ob = Go
  -- corec G Go GF .F-hom {x}{y} f =
  --   transport (λ i → C [ GF i x , GF i y ]) (G .F-hom f)
  -- corec G Go GF .F-id = {!!}
  -- corec G Go GF .F-seq = {!!}
