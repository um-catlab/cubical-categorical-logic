{-
  Yoneda strictification of an uncurried displayed presheaf.
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Strict where

open import Cubical.Foundations.Prelude

import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.Strict
open import Cubical.Categories.Instances.Strictify
open import Cubical.Categories.Instances.TotalCategory

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.StrictHom
open import Cubical.Categories.Displayed.Instances.Strictify

private
  variable
    ℓP ℓPᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Functor
open Categoryᴰ
open StructureOver
open PshHomStrictᴰ

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) where
  private
    module P = PresheafNotation P

  EqElementStrictStr : StructureOver (YonedaStrictify C) _ _
  EqElementStrictStr .ob[_] = P.p[_]
  EqElementStrictStr .Hom[_][_,_] f p q = (f P.⋆ q) Eq.≡ p
  EqElementStrictStr .idᴰ = Eq.refl
  EqElementStrictStr ._⋆ᴰ_ Eq.refl Eq.refl = Eq.refl
  EqElementStrictStr .isPropHomᴰ = Eq.isSet→isSetEq P.isSetPsh

  EqElementStrict : Categoryᴰ (YonedaStrictify C) _ _
  EqElementStrict = StructureOver→Catᴰ EqElementStrictStr

module _ {C : Category ℓC ℓC'} where
  _/Strict_ : (Cᴰ : Categoryᴰ (YonedaStrictify C) ℓCᴰ ℓCᴰ') (P : Presheaf C ℓP)
            → Category _ _
  Cᴰ /Strict P = ∫C (Cᴰ ×ᴰ EqElementStrict P)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where

  YonedaStrictifyPshᴰ : Presheaf (YonedaStrictifyᴰ Cᴰ /Strict P) _
  YonedaStrictifyPshᴰ .F-ob (c , cᴰ , α) .fst = PshHomStrictᴰ α (Cᴰ [-][-, cᴰ ]) Pᴰ
  YonedaStrictifyPshᴰ .F-ob (c , cᴰ , α) .snd = isSetPshHomStrictᴰ _ _ _
  YonedaStrictifyPshᴰ .F-hom (f , fᴰ , Eq.refl) pᴰ = fᴰ ⋆PshHomStrictᴰ pᴰ
  YonedaStrictifyPshᴰ .F-id = refl
  YonedaStrictifyPshᴰ .F-seq (_ , _ , Eq.refl) (_ , _ , Eq.refl) = refl
