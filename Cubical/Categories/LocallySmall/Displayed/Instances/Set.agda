module Cubical.Categories.LocallySmall.Displayed.Instances.Set where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Set
open import Cubical.Categories.LocallySmall.Constructions.BinProduct

open import Cubical.Categories.LocallySmall.Displayed
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total

open Category
open Categoryᴰ
open Σω

SETᴰ : SmallFibersᴰCategoryᴰ SET
  Level _
  (λ (liftω ℓ) A ℓ' → ⟨ A ⟩ → hSet ℓ') _
SETᴰ .Hom[_][_,_] {x = _ , liftω A}{y = _ , liftω B}
  (_ , f) (liftω ℓA , liftω Aᴰ) (liftω ℓB , liftω Bᴰ) =
    ∀ (a : ⟨ A ⟩) → ⟨ Aᴰ a ⟩ → ⟨ Bᴰ (f a) ⟩
SETᴰ .idᴰ = λ a z → z
SETᴰ ._⋆ᴰ_ {f = _ , f} fᴰ gᴰ x xᴰ = gᴰ (f x) (fᴰ x xᴰ)
SETᴰ .⋆IdLᴰ _ = refl
SETᴰ .⋆IdRᴰ _ = refl
SETᴰ .⋆Assocᴰ _ _ _ = refl
SETᴰ .isSetHomᴰ {yᴰ = liftω ℓB , liftω Bᴰ} =
  isSetΠ2 λ _ _ → Bᴰ _ .snd

-- module _ {ℓ ℓ'} where
--   private
--     module SETᴰ = ∫CᴰSETᴰNotation

--   ΣF :
--     Functor
--       (∫C (SETᴰ.vᴰ[ (liftω ℓ) , (liftω ℓ') ]SF))
--       SET.v[ liftω (ℓ-max ℓ ℓ') ]
--   ΣF .F-ob (liftω A , liftω B) =
--     liftω ((Σ[ a ∈ ⟨ A ⟩ ] ⟨ B a ⟩) ,
--            isSetΣ (A .snd) λ x → B x .snd)
--   ΣF .F-hom (f , g) (x , y) = f x , g x y
--   ΣF .F-id = refl
--   ΣF .F-seq _ _ = funExt λ x →
--     {!!}
