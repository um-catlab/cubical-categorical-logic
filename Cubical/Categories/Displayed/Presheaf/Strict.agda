{-
  Yoneda strictification of a curried displayed presheaf.
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Strict where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.Strict
open import Cubical.Categories.Instances.Strictify

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.StrictHom

private
  variable
    ℓP ℓPᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Functor
open Functorᴰ
open Categoryᴰ
open PshHomStrictᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  YonedaStrictifyᴰ
    : Categoryᴰ (YonedaStrictify C)
        ℓCᴰ
        (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))

  -- Using curried pshs instead of uncurried
  YonedaStrictifyᴰ .ob[_] = Cᴰ .ob[_]
  YonedaStrictifyᴰ .Hom[_][_,_] α xᴰ yᴰ =
    PshHomStrictᴰ α (Cᴰ [-][-, xᴰ ]) (Cᴰ [-][-, yᴰ ])
  YonedaStrictifyᴰ .idᴰ = idPshHomStrictᴰ
  YonedaStrictifyᴰ ._⋆ᴰ_ = _⋆PshHomStrictᴰ_
  YonedaStrictifyᴰ .⋆IdLᴰ _ = refl
  YonedaStrictifyᴰ .⋆IdRᴰ _ = refl
  YonedaStrictifyᴰ .⋆Assocᴰ _ _ _ = refl
  YonedaStrictifyᴰ .isSetHomᴰ = isSetPshHomStrictᴰ _ _ _

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where

  YonedaStrictifyPshᴰ : Presheafᴰ (YonedaStrictifyPsh P) (YonedaStrictifyᴰ Cᴰ) _
  YonedaStrictifyPshᴰ .F-obᴰ cᴰ α .fst = PshHomStrictᴰ α (Cᴰ [-][-, cᴰ ]) Pᴰ
  YonedaStrictifyPshᴰ .F-obᴰ cᴰ α .snd = isSetPshHomStrictᴰ _ _ _
  YonedaStrictifyPshᴰ .F-homᴰ fᴰ α pᴰ = fᴰ ⋆PshHomStrictᴰ pᴰ
  YonedaStrictifyPshᴰ .F-idᴰ = refl
  YonedaStrictifyPshᴰ .F-seqᴰ fᴰ gᴰ = refl
