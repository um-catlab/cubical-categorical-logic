module Cubical.Categories.LocallySmall.Presheaf.Constructions.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Functor.Constant
open import Cubical.Categories.LocallySmall.NaturalTransformation.SmallFibered
open import Cubical.Categories.LocallySmall.Presheaf.Base

open Functor
open SmallFibNatTrans

module _ {C : SmallCategory ℓC ℓC'} where
  UnitPsh : Presheaf C ℓ-zero
  UnitPsh = Constant (liftω (Unit , isSetUnit))

  UnitPsh-intro : ∀ {ℓP} → {P : Presheaf C ℓP} → PSH.Hom[ ⟨ P ⟩Psh , ⟨ UnitPsh ⟩Psh ]
  UnitPsh-intro .fst = tt
  UnitPsh-intro .snd .N-ob = λ x _ → tt
  UnitPsh-intro .snd .N-hom = λ _ → refl
