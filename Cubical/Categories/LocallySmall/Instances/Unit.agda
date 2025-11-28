module Cubical.Categories.LocallySmall.Instances.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma.More
open import Cubical.Data.Unit

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Indiscrete

open Category
open Σω

UNIT : GloballySmallCategory (Liftω Unit) ℓ-zero
UNIT = Indiscrete (Liftω Unit)

SmallUNIT : SmallCategory ℓ-zero ℓ-zero
SmallUNIT = smallcat _ UNIT

module _ {C : Category Cob CHom-ℓ} (c : Cob) where
  -- TODO: delete elimUNIT, wrong terminology
  elimUNIT : Functor UNIT C
  elimUNIT .Functor.F-ob = λ z → c
  elimUNIT .Functor.F-hom = λ z → id C
  elimUNIT .Functor.F-id = refl
  elimUNIT .Functor.F-seq = λ _ _ → sym (⋆IdR C _)

  rec : Functor UNIT C
  rec = elimUNIT

module _ {C : Category Cob CHom-ℓ} where
  introUNIT : Functor C UNIT
  introUNIT .Functor.F-ob = λ _ → liftω tt
  introUNIT .Functor.F-hom = λ _ → tt
  introUNIT .Functor.F-id = refl
  introUNIT .Functor.F-seq = λ _ _ → refl
