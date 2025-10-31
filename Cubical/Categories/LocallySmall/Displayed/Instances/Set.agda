module Cubical.Categories.LocallySmall.Displayed.Instances.Set where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Set
open import Cubical.Categories.LocallySmall.Constructions.BinProduct

open import Cubical.Categories.LocallySmall.Displayed
open import Cubical.Categories.LocallySmall.Displayed.SmallFibers

open Category
open Categoryᴰ
open Σω

SETᴰ :
  SmallFibersᴰCategoryᴰ SET LEVEL _
  (λ ((liftω ℓ , liftω A) , liftω ℓ') → ⟨ A ⟩ → hSet ℓ')
    _
SETᴰ .Hom[_][_,_] {x = (_ , liftω A) , _}
  ((_ , f) , _) (liftω Aᴰ) (liftω Bᴰ) =
    ∀ (a : ⟨ A ⟩) → ⟨ Aᴰ a ⟩ → ⟨ Bᴰ (f a) ⟩
SETᴰ .idᴰ = λ a z → z
SETᴰ ._⋆ᴰ_ {f = (_ , f), _} fᴰ gᴰ a aᴰ = gᴰ (f a) (fᴰ a aᴰ)
SETᴰ .⋆IdLᴰ = λ _ → refl
SETᴰ .⋆IdRᴰ = λ _ → refl
SETᴰ .⋆Assocᴰ = λ _ _ _ → refl
SETᴰ .isSetHomᴰ {yᴰ = liftω Bᴰ} = isSetΠ2 λ _ _ → Bᴰ _ .snd
