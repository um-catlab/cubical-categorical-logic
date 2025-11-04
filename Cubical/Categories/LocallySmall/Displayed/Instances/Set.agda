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
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex
open import Cubical.Categories.LocallySmall.Displayed.SmallFibers

open Category
open Categoryᴰ
open Σω

-- SETᴰ over ∫C (weaken SET.∫C LEVEL)
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

private
  module SET = CategoryᴰNotation SET
  module SETᴰ = SmallFibersᴰCategoryᴰNotation SETᴰ

SETᴰ' : Categoryᴰ (LEVEL ×C LEVEL) _ _
SETᴰ' = ∫Cᴰ _ (reindexEqSF F SETᴰ Eq.refl (λ _ _ → Eq.refl))
  where
  SET' : SmallFibersCategoryᴰ _ _ _ _
  SET' = reindexEqSF ℓ-MAX SET Eq.refl (λ _ _ → Eq.refl)

  F : Functor (∫C SET') (∫C (weaken SET.∫C LEVEL))
  F .Functor.F-ob = λ z →
                       (liftω
                        (ℓ-max (z .fst .fst .Liftω.lowerω) (z .fst .snd .Liftω.lowerω))
                        , z .snd)
                       , z .fst .snd
  F .Functor.F-hom = λ z → (tt , z .snd) , tt
  F .Functor.F-id = refl
  F .Functor.F-seq = λ _ _ → refl

SETᴰ'' : Categoryᴰ (LEVEL ×C LEVEL) _ _
SETᴰ'' =
  reindexEqSF
    ℓ-MAX
    (∫CᴰSF SET (reindexEqSF F SETᴰ Eq.refl (λ _ _ → Eq.refl))) Eq.refl λ _ _ → Eq.refl
  where
  SET' : SmallFibersCategoryᴰ _ _ _ _
  SET' = reindexEqSF ℓ-MAX SET Eq.refl (λ _ _ → Eq.refl)

  F : Functor (∫C SET) (∫C (weaken SET.∫C LEVEL))
  F .Functor.F-ob = λ z → z , z .fst
  F .Functor.F-hom = λ z → z , tt
  F .Functor.F-id = refl
  F .Functor.F-seq = λ _ _ → refl

SETᴰ''' : SmallFibersCategoryᴰ (LEVEL ×C LEVEL) _ _ _
SETᴰ''' = ∫CᴰSF _ (reindexEqSF F SETᴰ Eq.refl (λ _ _ → Eq.refl))
  where

  SET' : SmallFibersCategoryᴰ _ _ _ _
  SET' = reindexEqSF (π₁ LEVEL LEVEL) SET Eq.refl (λ _ _ → Eq.refl)

  F : Functor (∫C SET') (∫C (weaken SET.∫C LEVEL))
  F .Functor.F-ob = λ z → (z .fst .fst , z .snd) , z .fst .snd
  F .Functor.F-hom = λ z → (tt , z .snd) , tt
  F .Functor.F-id = refl
  F .Functor.F-seq = λ _ _ → refl

-- open Functor
-- -- module _ {ℓ ℓ'} where
--   -- ΣF : Functor (∫C ⟨ SETᴰ.vᴰ[ liftω ℓ ][ liftω ℓ' ] ⟩smallcatᴰ)
--   --               SET.v[ liftω (ℓ-max ℓ ℓ') ]
--   -- ΣF .F-ob (liftω A , liftω B) =
--   --   liftω ((Σ[ a ∈ ⟨ A ⟩ ] ⟨ B a ⟩) , isSetΣ (A .snd) λ a → B a .snd)
--   -- ΣF .F-hom (f , g) (x , y) = f x , g x y
--   -- ΣF .F-id = refl
--   -- ΣF .F-seq (f , g) (f' , g') = {!!}
--   --   -- i (x , y) =
--   --   -- transport refl (f' (f (transport refl x))) , {!!}

-- private
--   F-ℓ-max : Functor (∫C (weaken SET.∫C LEVEL)) LEVEL
--   F-ℓ-max .F-ob ((liftω ℓ , liftω A) , liftω ℓ') = liftω (ℓ-max ℓ ℓ')
--   F-ℓ-max .F-hom = λ _ → tt
--   F-ℓ-max .F-id = refl
--   F-ℓ-max .F-seq = λ _ _ → refl

-- open Functorᴰ
-- ΣF : Functorᴰ F-ℓ-max SETᴰ SET
-- ΣF .F-obᴰ {x = (liftω ℓ , liftω A) , liftω ℓ'} (liftω B) =
--   liftω ((Σ[ a ∈ ⟨ A ⟩ ] ⟨ B a ⟩) , isSetΣ (A .snd) λ a → B a .snd)
-- ΣF .F-homᴰ {f = (_ , f) , _} fᴰ (x , y) = f x , fᴰ x y
-- ΣF .F-idᴰ = refl
-- ΣF .F-seqᴰ = λ _ _ → refl

-- ΣF'' : Functorᴰ {!!} (∫Cᴰ _ SETᴰ) SET
-- ΣF'' = {!!}
-- -- ΣF .F-obᴰ {x = (liftω ℓ , liftω A) , liftω ℓ'} (liftω B) =
-- --   liftω ((Σ[ a ∈ ⟨ A ⟩ ] ⟨ B a ⟩) , isSetΣ (A .snd) λ a → B a .snd)
-- -- ΣF .F-homᴰ {f = (_ , f) , _} fᴰ (x , y) = f x , fᴰ x y
-- -- ΣF .F-idᴰ = refl
-- -- ΣF .F-seqᴰ = λ _ _ → refl

-- module _ {ℓ ℓ'} where
--   private
--     module ΣF = FunctorᴰNotation ΣF
--     module SETᴰ' = CategoryᴰNotation SETᴰ'
--   ΣF' : Functor SETᴰ'.v[ liftω ℓ , liftω ℓ' ]
--                 SET.v[ liftω (ℓ-max ℓ ℓ') ]
--   ΣF' = Fv Gᴰ (liftω ℓ , liftω ℓ')
--     where
--     Gᴰ : Functorᴰ ℓ-MAX SETᴰ' SET
--     Gᴰ .F-obᴰ = λ z → z .fst
--     Gᴰ .F-homᴰ = λ fᴰ → fᴰ .fst
--     Gᴰ .F-idᴰ = refl
--     Gᴰ .F-seqᴰ = λ _ _ → refl
