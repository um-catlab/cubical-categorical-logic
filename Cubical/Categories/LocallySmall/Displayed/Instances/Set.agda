module Cubical.Categories.LocallySmall.Displayed.Instances.Set where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Set
open import Cubical.Categories.LocallySmall.Constructions.BinProduct

open import Cubical.Categories.LocallySmall.Displayed.Base

open Category
open Categoryᴰ
open Σω


SETᴰ :
  SmallFibersCategoryᴰ (∫C SET ×C LEVEL) _
    (λ ((liftω ℓ , liftω A) , liftω ℓ') → ⟨ A ⟩ → hSet ℓ')
    _
SETᴰ .Hom[_][_,_] ((_ , f), _) (liftω A) (liftω B) =
  ∀ x → ⟨ A x ⟩ → ⟨ B (f x) ⟩
SETᴰ .idᴰ = λ x z → z
SETᴰ ._⋆ᴰ_ {f = ((_ , f), _)} {((_ , g), _)}
  fᴰ gᴰ x xᴰ = gᴰ (f x) (fᴰ x xᴰ)
SETᴰ .⋆IdLᴰ _ = refl
SETᴰ .⋆IdRᴰ _ = refl
SETᴰ .⋆Assocᴰ _ _ _ = refl
SETᴰ .isSetHomᴰ {yᴰ = liftω B} = isSetΠ2 (λ _ _ → B _ .snd)
