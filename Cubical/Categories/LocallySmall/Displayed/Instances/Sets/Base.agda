{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Constructions.BinProduct.Base
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Instances.Level

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.SmallDisplayedFibers
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Bifunctor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken.Properties

open Category
open Categoryᴰ
open Σω

SET : SmallFibersCategoryᴰ LEVEL _ (λ (liftω ℓ) → hSet ℓ) _
SET .Hom[_][_,_] _ (liftω X) (liftω Y) = ⟨ X ⟩ → ⟨ Y ⟩
SET .idᴰ = λ z → z
SET ._⋆ᴰ_ = λ g f x → f (g x)
SET .⋆IdLᴰ = λ _ → refl
SET .⋆IdRᴰ = λ _ → refl
SET .⋆Assocᴰ = λ _ _ _ → refl
SET .isSetHomᴰ {yᴰ = (liftω Y)} = isSet→ (Y .snd)

open Bifunctorᴰ
×SETBif : Bifunctorᴰ ℓ-MAXBif SET SET SET
×SETBif .Bif-obᴰ (liftω A) (liftω B) =
  liftω (⟨ A ⟩ × ⟨ B ⟩ , isSet× (A .snd) (B .snd))
×SETBif .Bif-hom×ᴰ = λ fᴰ gᴰ z → fᴰ (z .fst) , gᴰ (z .snd)
×SETBif .Bif-homLᴰ = λ fᴰ dᴰ z → fᴰ (z .fst) , z .snd
×SETBif .Bif-homRᴰ = λ cᴰ gᴰ z → z .fst , gᴰ (z .snd)
×SETBif .Bif-×-idᴰ = refl
×SETBif .Bif-×-seqᴰ = refl
×SETBif .Bif-L×-agreeᴰ _ _ = refl
×SETBif .Bif-R×-agreeᴰ _ _ = refl

×SET : Functorᴰ ℓ-MAX (SET ×CᴰSF SET) SET
×SET = BifunctorᴰToParFunctorᴰSF ×SETBif

private
  module SET = CategoryᴰNotation SET

SETᴰ : SmallFibersᴰCategoryᴰ (weaken LEVEL LEVEL) SET _
  (λ (liftω ℓ , (liftω ℓ' , liftω A)) → ⟨ A ⟩ → hSet ℓ')
  _
SETᴰ .Hom[_][_,_] {x = _ , (_ , liftω A)} (_ , _ , f) (liftω Aᴰ) (liftω Bᴰ) =
    ∀ (a : ⟨ A ⟩) → ⟨ Aᴰ a ⟩ → ⟨ Bᴰ (f a) ⟩
SETᴰ .idᴰ = λ a z → z
SETᴰ ._⋆ᴰ_ {f = _ , _ , f} fᴰ gᴰ a aᴰ = gᴰ (f a) (fᴰ a aᴰ)
SETᴰ .⋆IdLᴰ = λ _ → refl
SETᴰ .⋆IdRᴰ = λ _ → refl
SETᴰ .⋆Assocᴰ = λ _ _ _ → refl
SETᴰ .isSetHomᴰ {yᴰ = liftω Bᴰ} = isSetΠ2 λ _ _ → Bᴰ _ .snd

private
  module SETᴰ = SmallFibersᴰNotation SETᴰ
  module SETⱽ {ℓ} = Category SET.v[ liftω ℓ ]
  module SETⱽᴰ {ℓ}{ℓ'} = CategoryᴰNotation SETᴰ.vᴰ[ liftω ℓ ][ liftω ℓ' ]

SETAt : (ℓ : Level) → SmallCategory _ _
SETAt ℓ = smallcat _ SET.v[ liftω ℓ ]

SETAtEq : (ℓ : Level) → SmallCategory _ _
SETAtEq ℓ = smallcat _ (fibEq SET Eq.refl (liftω ℓ))

SETᴰAt : (ℓ ℓ' : Level) → SmallCategoryᴰ (SETAt ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
SETᴰAt ℓ ℓ' = smallcatᴰ _ SETᴰ.vᴰ[ liftω ℓ ][ liftω ℓ' ]

SETᴰAtEq : (ℓ ℓ' : Level) → SmallCategoryᴰ (SETAtEq ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
SETᴰAtEq ℓ ℓ' = smallcatᴰ _
  (fibᴰEq LEVEL (weaken LEVEL LEVEL) SET SETᴰ (liftω ℓ) (liftω ℓ')
    Eq.refl (λ _ _ → Eq.refl))

ΣF : ∀ ℓ ℓ' → Functor
  (∫C (SETᴰAtEq ℓ ℓ' .SmallCategoryᴰ.catᴰ))
  (SETAtEq (ℓ-max ℓ ℓ') .SmallCategory.cat)
ΣF ℓ ℓ' .Functor.F-ob (liftω A , liftω B) =
  liftω (_ , (isSetΣ (A .snd) (λ a → B a .snd)))
ΣF ℓ ℓ' .Functor.F-hom (f , g) (x , y) = f x , g x y
ΣF ℓ ℓ' .Functor.F-id = refl
ΣF ℓ ℓ' .Functor.F-seq = λ _ _ → refl
