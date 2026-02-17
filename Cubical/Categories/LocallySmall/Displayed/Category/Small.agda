module Cubical.Categories.LocallySmall.Displayed.Category.Small where

-- open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

import Cubical.Categories.Category as Small
import Cubical.Categories.Displayed.Base as Smallᴰ

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base

open Category
open Categoryᴰ
open Σω
open Liftω

-- Displayed categories whose fibers are *small* categories.
-- This means:
-- 1. The type of displayed objects over any fixed object is small
-- 2. The type of displayed hom sets is small and the level only
-- depends on the base objects.
module _ (C : Category Cob CHom-ℓ) where
  private
    module C = Category C
  module _ (obᴰ-ℓ : Cob → Level) (obᴰ : ∀ x → Type (obᴰ-ℓ x))
    (Homᴰ-ℓ : ∀ (x y : Cob) → Level) where
    SmallFibersCategoryᴰ : Typeω
    SmallFibersCategoryᴰ = Categoryᴰ C (λ x → Liftω (obᴰ x)) λ x y _ _ → Homᴰ-ℓ x y

module _ (C : Category Cob CHom-ℓ) where
  private
    module C = Category C

  SmallObjectsCategoryᴰ :
    (obᴰ-ℓ : Cob → Level) (Cobᴰ : (x : Cob) → Type (obᴰ-ℓ x))
    (CHom-ℓᴰ : (x y : Cob) → Liftω (Cobᴰ x) → Liftω (Cobᴰ y) → Level) → Typeω
  SmallObjectsCategoryᴰ obᴰ-ℓ Cobᴰ CHom-ℓᴰ = Categoryᴰ C (λ x → Liftω (Cobᴰ x)) CHom-ℓᴰ

module _
  {Cob : Type ℓC}
  {CHom-ℓ}
  {C : SmallObjectsCategory Cob CHom-ℓ}
  {Cobᴰ-ℓ : Level}
  {Cobᴰ CHom-ℓᴰ}
  (Cᴰ : SmallObjectsCategoryᴰ C (λ _ → Cobᴰ-ℓ) Cobᴰ CHom-ℓᴰ)
  where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ

  ∫Csmallobs : SmallObjectsCategory (Σ Cob λ c → Cobᴰ (liftω c)) _
  ∫Csmallobs .Hom[_,_] (liftω (c , cᴰ)) (liftω (d , dᴰ)) =
    Cᴰ.∫Hom[ (liftω c , liftω cᴰ) , (liftω d , liftω dᴰ) ]
  ∫Csmallobs .id = C.id , Cᴰ.idᴰ
  ∫Csmallobs ._⋆_ = λ f g → f .fst C.⋆ g .fst , f .snd Cᴰ.⋆ᴰ g .snd
  ∫Csmallobs .⋆IdL = λ f → Cᴰ.⋆IdLᴰ (f .snd)
  ∫Csmallobs .⋆IdR = λ f → Cᴰ.⋆IdRᴰ (f .snd)
  ∫Csmallobs .⋆Assoc = λ f g h → Cᴰ.⋆Assocᴰ (f .snd) (g .snd) (h .snd)
  ∫Csmallobs .isSetHom = isSetΣ C.isSetHom (λ _ → Cᴰ.isSetHomᴰ)

module _ (C : Category Cob CHom-ℓ) where
  private
    module C = Category C

  GloballySmallCategoryᴰ : (Cobᴰ : C.Ob → Typeω) (ℓCᴰ' : Level) → Typeω
  GloballySmallCategoryᴰ Cobᴰ ℓCᴰ' = Categoryᴰ C Cobᴰ λ _ _ _ _ → ℓCᴰ'

  SmallObjectsGloballySmallCategoryᴰ :
    (obᴰ-ℓ : Cob → Level) (Cobᴰ : (x : Cob) → Type (obᴰ-ℓ x))
    (ℓCᴰ' : Level) → Typeω
  SmallObjectsGloballySmallCategoryᴰ obᴰ-ℓ Cobᴰ ℓCᴰ' = SmallObjectsCategoryᴰ C obᴰ-ℓ Cobᴰ (λ _ _ _ _ → ℓCᴰ')

module _ (C : SmallCategory ℓC ℓC') where
  private
    module C = SmallCategory C

  record SmallCategoryᴰ (ℓCᴰ ℓCᴰ' : Level) : Typeω where
    constructor smallcatᴰ
    field
       obᴰ : C.ob → Type ℓCᴰ
       catᴰ : GloballySmallCategoryᴰ C.cat (mapω' obᴰ) ℓCᴰ'
    private
      module Cᴰ = Categoryᴰ catᴰ

    open SmallCategory
    ∫Csmall : SmallCategory _ _
    ∫Csmall .ob = Σ C.ob obᴰ
    ∫Csmall .cat .Hom[_,_] (liftω (c , cᴰ)) (liftω (d , dᴰ)) =
      Cᴰ.∫Hom[ (liftω c , liftω cᴰ) , (liftω d , liftω dᴰ) ]
    ∫Csmall .cat .id = C.id , Cᴰ.idᴰ
    ∫Csmall .cat ._⋆_ = λ f g → f .fst C.⋆ g .fst , f .snd Cᴰ.⋆ᴰ g .snd
    ∫Csmall .cat .⋆IdL = λ f → Cᴰ.⋆IdLᴰ (f .snd)
    ∫Csmall .cat .⋆IdR = λ f → Cᴰ.⋆IdRᴰ (f .snd)
    ∫Csmall .cat .⋆Assoc = λ f g h → Cᴰ.⋆Assocᴰ (f .snd) (g .snd) (h .snd)
    ∫Csmall .cat .isSetHom = isSetΣ C.isSetHom (λ _ → Cᴰ.isSetHomᴰ)

    open Cᴰ public

open SmallCategory
open SmallCategoryᴰ

module _
  {C : SmallCategory ℓC ℓC'}
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  where
  private
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ

  _^opsmallᴰ : SmallCategoryᴰ (C ^opsmall) ℓCᴰ ℓCᴰ'
  _^opsmallᴰ = smallcatᴰ Cᴰ.obᴰ (Cᴰ.catᴰ ^opᴰ)

module _
  {C : Small.Category ℓC ℓC'}
  (Cᴰ : Smallᴰ.Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Small.Category C
    module Cᴰ = Smallᴰ.Categoryᴰ Cᴰ

  |mkSmallCategoryᴰ| :
    GloballySmallCategoryᴰ ((mkSmallCategory C) .cat) (mapω' Cᴰ.ob[_]) ℓCᴰ'
  |mkSmallCategoryᴰ| .Hom[_][_,_] f (liftω xᴰ) (liftω yᴰ) =
    Cᴰ.Hom[ f ][ xᴰ , yᴰ ]
  |mkSmallCategoryᴰ| .idᴰ = Cᴰ.idᴰ
  |mkSmallCategoryᴰ| ._⋆ᴰ_ = Cᴰ._⋆ᴰ_
  |mkSmallCategoryᴰ| .⋆IdLᴰ fᴰ = ΣPathP ((C.⋆IdL _) , (Cᴰ.⋆IdLᴰ fᴰ))
  |mkSmallCategoryᴰ| .⋆IdRᴰ fᴰ = ΣPathP ((λ i → C.⋆IdR _ i) , Cᴰ.⋆IdRᴰ fᴰ)
  |mkSmallCategoryᴰ| .⋆Assocᴰ fᴰ gᴰ hᴰ = ΣPathP ((C.⋆Assoc _ _ _) , (Cᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ))
  |mkSmallCategoryᴰ| .isSetHomᴰ = Cᴰ.isSetHomᴰ

  mkSmallCategoryᴰ : SmallCategoryᴰ (mkSmallCategory C) ℓCᴰ ℓCᴰ'
  mkSmallCategoryᴰ = smallcatᴰ Cᴰ.ob[_] |mkSmallCategoryᴰ|


module _
  {C : SmallCategory ℓC ℓC'}
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  where
  open Small.Category
  open Smallᴰ.Categoryᴰ
  private
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ

  SmallLocallySmallCategoryᴰ→SmallCategoryᴰ :
    Smallᴰ.Categoryᴰ (SmallLocallySmallCategory→SmallCategory C) ℓCᴰ ℓCᴰ'
  SmallLocallySmallCategoryᴰ→SmallCategoryᴰ .ob[_] = Cᴰ.obᴰ
  SmallLocallySmallCategoryᴰ→SmallCategoryᴰ .Hom[_][_,_] f xᴰ yᴰ =
    Cᴰ.Hom[ f ][ liftω xᴰ , liftω yᴰ ]
  SmallLocallySmallCategoryᴰ→SmallCategoryᴰ .idᴰ = Cᴰ.idᴰ
  SmallLocallySmallCategoryᴰ→SmallCategoryᴰ ._⋆ᴰ_ = Cᴰ._⋆ᴰ_
  SmallLocallySmallCategoryᴰ→SmallCategoryᴰ .⋆IdLᴰ _ =
    Cᴰ.rectify $ Cᴰ.≡out (Cᴰ.⋆IdLᴰ _)
  SmallLocallySmallCategoryᴰ→SmallCategoryᴰ .⋆IdRᴰ _ =
    Cᴰ.rectify $ Cᴰ.≡out (Cᴰ.⋆IdRᴰ _)
  SmallLocallySmallCategoryᴰ→SmallCategoryᴰ .⋆Assocᴰ _ _ _ =
    Cᴰ.rectify $ Cᴰ.≡out (Cᴰ.⋆Assocᴰ _ _ _)
  SmallLocallySmallCategoryᴰ→SmallCategoryᴰ .isSetHomᴰ = Cᴰ.isSetHomᴰ
