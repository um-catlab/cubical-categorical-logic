{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Displayed.Presheaf.GloballySmall.IntoFiberCategory.Base where

open import Cubical.Foundations.Prelude

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma.More


open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Functor using (_∘F_ ; _^opF)
import Cubical.Categories.LocallySmall.Functor as LocallySmallF
open import Cubical.Categories.LocallySmall.Presheaf.GloballySmall.IntoFiberCategory.Base

open import Cubical.Categories.LocallySmall.Displayed.Category
open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base
open import Cubical.Categories.LocallySmall.Displayed.Instances.Functor.IntoFiberCategory
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base using (_∘Fᴰ_)
import Cubical.Categories.LocallySmall.Displayed.Functor.Base as LocallySmallFᴰ
open import Cubical.Categories.LocallySmall.Displayed.Functor.Properties using (_^opFᴰ)
open import Cubical.Categories.LocallySmall.Displayed.Instances.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Instances.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.IntoFiberCategory.Base
open import Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.IntoFiberCategory.Eq

open Σω
open Liftω
open LocallySmallF.Functor
open LocallySmallFᴰ.Functorᴰ

private
  module SET = CategoryᴰNotation SET
  module SETᴰ = SmallFibersᴰNotation SETᴰ

module _ {C : SmallCategory ℓC ℓC'} (P : Presheaf C ℓP) (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ
    module CᴰNotation = CategoryᴰNotation (Cᴰ.catᴰ)

  open NatTransᴰDefs (Cᴰ ^opsmallᴰ) (weaken LEVEL LEVEL) SET SETᴰ
  open FunctorEqᴰDefs (Cᴰ ^opsmallᴰ) (weaken LEVEL LEVEL) SET SETᴰ

  Presheafᴰ : Level → Typeω
  Presheafᴰ ℓPᴰ = FunctorEqᴰ Eq.refl (λ _ _ → Eq.refl) P (liftω ℓPᴰ)

  module _ (Pᴰ : Presheafᴰ ℓPᴰ) where
    ∫P : Presheaf Cᴰ.∫Csmall (ℓ-max ℓP ℓPᴰ)
    ∫P = ΣF ℓP ℓPᴰ ∘F ∫F Pᴰ ∘F F
      where
      F : LocallySmallF.Functor
        (SmallCategory.cat (Cᴰ.∫Csmall ^opsmall))
        (Categoryᴰ.∫C (SmallCategoryᴰ.catᴰ (Cᴰ ^opsmallᴰ)))
      F .F-ob = λ z → liftω (z .lowerω .fst) , liftω (z .lowerω .snd)
      F .F-hom = λ z → z
      F .F-id = refl
      F .F-seq = λ _ _ → refl

module _ {C : SmallCategory ℓC ℓC'} (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    PSH = PRESHEAF C
    LEVEL×PSH = weaken LEVEL LEVEL ×ᴰ PRESHEAF C
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ
    module LEVEL×PSH = CategoryᴰNotation LEVEL×PSH

  open FunctorEqᴰDefs (Cᴰ ^opsmallᴰ) (weaken LEVEL LEVEL) SET SETᴰ

  -- PRESHEAFᴰ is displayed over LEVEL×PSH
  -- where
  -- LEVEL×PSH is the fiberwise product of the category of
  -- levels weakened over itself and the displayed
  -- category of globally small presheaves
  --
  --         PRESHEAFᴰ
  --             |
  --             v
  --    /  LEVEL × PRESHEAF \
  --  ∫ |        |          |
  --    |        v          |
  --    \      LEVEL        /
  PRESHEAFᴰ : Categoryᴰ LEVEL×PSH.∫C _ _
  PRESHEAFᴰ = FUNCTOR-EQᴰ (Cᴰ ^opsmallᴰ) (weaken LEVEL LEVEL) SET SETᴰ
    Eq.refl (λ _ _ _ _ → Eq.refl)

module _ {C : SmallCategory ℓC ℓC'} (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    PSH = PRESHEAF C
    LEVEL×PSH = weaken LEVEL LEVEL ×ᴰ PRESHEAF C
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ
    module LEVEL×PSH = CategoryᴰNotation LEVEL×PSH

  private
    module PSHᴰ = CategoryᴰNotation (PRESHEAFᴰ Cᴰ)
    module PSHISOᴰ = CategoryᴰNotation PSHᴰ.ISOCᴰ

  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    (α : PshHom P Q)
    (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where

    PshHomᴰ : Type _
    PshHomᴰ = PSHᴰ.Hom[ _ , _ , α ][ Pᴰ , Qᴰ ]

  module _ {D : SmallCategory ℓD ℓDᴰ'} {Dᴰ : SmallCategoryᴰ D ℓDᴰ ℓDᴰ'}
    where
    private
      module D = SmallCategory D
      module Dᴰ = SmallCategoryᴰ Dᴰ

    module _ {F : LocallySmallF.Functor (C.cat) (D.cat)}
      {P : Presheaf C ℓP} {Q : Presheaf D ℓQ}
      (α : PshHet F P Q)
      (Fᴰ : LocallySmallFᴰ.Functorᴰ F Cᴰ.catᴰ Dᴰ.catᴰ)
      (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ) where
      PshHetᴰ : Type _
      PshHetᴰ = PshHomᴰ α Pᴰ (Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ))
