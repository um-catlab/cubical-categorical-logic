module Cubical.Categories.LocallySmall.Presheaf.GloballySmall.IntoFiberCategory.Constructions.Unit.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Functor.Constant
open import Cubical.Categories.LocallySmall.NaturalTransformation.IntoFiberCategory
open import Cubical.Categories.LocallySmall.Presheaf.GloballySmall.IntoFiberCategory.Base

open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base

open Functor

module _ {C : SmallCategory ℓC ℓC'} where
  open NatTransDefs (C ^opsmall) SET
  open NatTrans

  UnitPsh : Presheaf C ℓ-zero
  UnitPsh = Constant (liftω (Unit , isSetUnit))

  UnitPsh-intro : ∀ {ℓP} → {P : Presheaf C ℓP} →
    PshHom {C = C} P UnitPsh
  UnitPsh-intro .N-ob = λ x _ → tt
  UnitPsh-intro .N-hom = λ _ → refl
