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


private
  module SET = CategoryᴰNotation SET

-- SETᴰ over ∫SET × LEVEL
SETᴰ' :
  SmallFibersCategoryᴰ (∫C SET ×C LEVEL) _
    (λ ((liftω ℓ , liftω A) , liftω ℓ') → ⟨ A ⟩ → hSet ℓ')
    _
SETᴰ' .Hom[_][_,_] ((_ , f), _) (liftω A) (liftω B) =
  ∀ x → ⟨ A x ⟩ → ⟨ B (f x) ⟩
SETᴰ' .idᴰ = λ x z → z
SETᴰ' ._⋆ᴰ_ {f = ((_ , f), _)} {((_ , g), _)}
  fᴰ gᴰ x xᴰ = gᴰ (f x) (fᴰ x xᴰ)
SETᴰ' .⋆IdLᴰ _ = refl
SETᴰ' .⋆IdRᴰ _ = refl
SETᴰ' .⋆Assocᴰ _ _ _ = refl
SETᴰ' .isSetHomᴰ {yᴰ = liftω B} = isSetΠ2 (λ _ _ → B _ .snd)

-- Reorganize the base category
-- Instead of the total category of (SET over LEVEL) paired with LEVEL,
-- directly display SET over LEVEL × LEVEL
weakenLevelSET : SmallFibersCategoryᴰ (LEVEL ×C LEVEL) _ _ _
weakenLevelSET = reindexEqSF (π₁ LEVEL LEVEL) SET Eq.refl λ _ _ → Eq.refl

private
  module weakenLevelSET = CategoryᴰNotation weakenLevelSET
module _ (ℓ ℓ' : Level) where
  open Functor
  SET→weakenLevelSET : Functor SET.v[ liftω ℓ ] weakenLevelSET.v[ liftω ℓ , liftω ℓ' ]
  SET→weakenLevelSET .F-ob = λ z → z
  SET→weakenLevelSET .F-hom = λ z → z
  SET→weakenLevelSET .F-id = refl
  SET→weakenLevelSET .F-seq _ _ = refl

open Functor
-- SETᴰ over ∫weakenLevelSET
SETᴰ'' :
  SmallFibersCategoryᴰ (∫C weakenLevelSET) _ _ _
SETᴰ'' = reindexEqSF F SETᴰ' Eq.refl (λ _ _ → Eq.refl)
  where
  F : Functor (∫C weakenLevelSET) (SET.∫C ×C LEVEL)
  F .F-ob = λ z → (z .fst .fst , z .snd) , z .fst .snd
  F .F-hom f = (_ , (f .snd)) , _
  F .F-id = refl
  F .F-seq _ _ = refl

open Liftω

-- Downstairs: (ℓ , ℓ') : Level × Level
-- Upstairs: (A , B) : Σ[ A ∈ hSet ℓ ] (⟨ A ⟩ → hSet ℓ')
SETᴰ : SmallFibersCategoryᴰ (LEVEL ×C LEVEL) _ _ _
SETᴰ = ∫CᴰSF weakenLevelSET SETᴰ''

-- module ∫CᴰSETᴰNotation = ∫CᴰSFNotation weakenLevelSET SETᴰ''
module ∫CᴰSETᴰNotation = ∫CᴰSFNotation weakenLevelSET SETᴰ''

module _ {ℓ ℓ'} where
  private
    module SETᴰ = ∫CᴰSETᴰNotation

  ΣF :
    Functor
      (∫C (SETᴰ.vᴰ[ (liftω ℓ) , (liftω ℓ') ]SF))
      SET.v[ liftω (ℓ-max ℓ ℓ') ]
  ΣF .F-ob (liftω A , liftω B) =
    liftω ((Σ[ a ∈ ⟨ A ⟩ ] ⟨ B a ⟩) ,
           isSetΣ (A .snd) λ x → B x .snd)
  ΣF .F-hom (f , g) (x , y) = f x , g x y
  ΣF .F-id = refl
  ΣF .F-seq _ _ = funExt λ x →
    {!!}


-- I avoided making this definition because it displays a level
-- but it might not actually matter that this doesn't have small fibers
--
-- I think the crucial bit is that it has "small fiber displayed categories"
-- What I mean, is when provided an element of the base cat of SET.∫C (a level)
-- and an element of the base cat of the disp cat (a level viewed as an index of
-- the Σω type below), then the resulting disp cat is a SmallCategoryᴰ
SETᴰ''' : Categoryᴰ SET.∫C
  (λ (liftω ℓ , liftω A) → Σω[ (liftω ℓ') ∈ Liftω Level ] Liftω (⟨ A ⟩ → hSet ℓ'))
  _
SETᴰ''' .Hom[_][_,_] {x = _ , liftω A}{y = _ , liftω B}
  (_ , f) (liftω ℓA , liftω Aᴰ) (liftω ℓB , liftω Bᴰ) =
    ∀ (a : ⟨ A ⟩) → ⟨ Aᴰ a ⟩ → ⟨ Bᴰ (f a) ⟩
SETᴰ''' .idᴰ = λ a z → z
SETᴰ''' ._⋆ᴰ_ {f = _ , f} fᴰ gᴰ x xᴰ = gᴰ (f x) (fᴰ x xᴰ)
SETᴰ''' .⋆IdLᴰ _ = refl
SETᴰ''' .⋆IdRᴰ _ = refl
SETᴰ''' .⋆Assocᴰ _ _ _ = refl
SETᴰ''' .isSetHomᴰ {yᴰ = liftω ℓB , liftω Bᴰ} =
  isSetΠ2 λ _ _ → Bᴰ _ .snd

module SmallDisplayedSets where
  open SmallDisplayedFiberCategoryᴰ SET SETᴰ'''

  -- This establishes that using vᴰ[_][_] works
  -- TODO now clean up this file to use SETᴰ'''
  smalldispsets : (ℓ ℓ' : Level) → SmallCategoryᴰ _ _ _
  smalldispsets ℓ ℓ' = vᴰ[ liftω ℓ ][ ℓ' ]
