{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Prod using (_×ω_; _,_)

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Instances.Functor.Fibered
open import Cubical.Categories.LocallySmall.NaturalTransformation.Fibered
open import Cubical.Categories.LocallySmall.Constructions.BinProduct.Base
open import Cubical.Categories.LocallySmall.Constructions.BinProduct.Properties
open import Cubical.Categories.LocallySmall.Constructions.Total.Properties as TotalCat

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Base

open Category
open Categoryᴰ
open Σω

module _
  {C : Category Cob CHom-ℓ}(Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  {D : Category Dob DHom-ℓ}(Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
    module D = CategoryNotation D
    module Dᴰ = Categoryᴰ Dᴰ

  _×Cᴰ_ : Categoryᴰ (C ×C D)
            (λ (c , d) → Σω[ cᴰ ∈ Cobᴰ c ] Dobᴰ d)
            _
  _×Cᴰ_ .Hom[_][_,_] (f , g) (c , d) (c' , d') =
    Cᴰ.Hom[ f ][ c , c' ] × Dᴰ.Hom[ g ][ d , d' ]
  _×Cᴰ_ .idᴰ = Cᴰ.idᴰ , Dᴰ.idᴰ
  _×Cᴰ_ ._⋆ᴰ_ (fᴰ , gᴰ) (fᴰ' , gᴰ') = fᴰ Cᴰ.⋆ᴰ fᴰ' , gᴰ Dᴰ.⋆ᴰ gᴰ'
  _×Cᴰ_ .⋆IdLᴰ _ =
    ΣPathP (
      ΣPathP ((C.⋆IdL _) , (D.⋆IdL _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdLᴰ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdLᴰ _)))
  _×Cᴰ_ .⋆IdRᴰ _ =
    ΣPathP (
      ΣPathP ((C.⋆IdR _) , (D.⋆IdR _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdRᴰ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdRᴰ _)))
  _×Cᴰ_ .⋆Assocᴰ _ _ _ =
    ΣPathP (
      ΣPathP ((C.⋆Assoc _ _ _) , (D.⋆Assoc _ _ _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆Assocᴰ _ _ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆Assocᴰ _ _ _)))
  _×Cᴰ_ .isSetHomᴰ = isSet× Cᴰ.isSetHomᴰ Dᴰ.isSetHomᴰ

  π₁ᴰ : Functorᴰ (π₁ C D) _×Cᴰ_ Cᴰ
  π₁ᴰ .Functorᴰ.F-obᴰ = λ z → z .fst
  π₁ᴰ .Functorᴰ.F-homᴰ = λ fᴰ → fᴰ .fst
  π₁ᴰ .Functorᴰ.F-idᴰ = refl
  π₁ᴰ .Functorᴰ.F-seqᴰ = λ _ _ → refl

  π₂ᴰ : Functorᴰ (π₂ C D) _×Cᴰ_ Dᴰ
  π₂ᴰ .Functorᴰ.F-obᴰ = λ z → z .snd
  π₂ᴰ .Functorᴰ.F-homᴰ = λ fᴰ → fᴰ .snd
  π₂ᴰ .Functorᴰ.F-idᴰ = refl
  π₂ᴰ .Functorᴰ.F-seqᴰ = λ _ _ → refl

module _
  {C : SmallCategory ℓC ℓC'}(Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  {D : SmallCategory ℓD ℓC'}(Dᴰ : SmallCategoryᴰ D ℓDᴰ ℓDᴰ')
  where
  private
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ
    module D = SmallCategory D
    module Dᴰ = SmallCategoryᴰ Dᴰ

  open SmallCategoryᴰ
  _×Cᴰsmall_ : SmallCategoryᴰ (C ×Csmall D) _ _
  _×Cᴰsmall_ .obᴰ (c , d) = Cᴰ.obᴰ c × Dᴰ.obᴰ d
  _×Cᴰsmall_ .catᴰ .Hom[_][_,_] (f , g)
    (liftω (c , d)) (liftω (c' , d')) =
    Cᴰ.Hom[ f ][ liftω c , liftω c' ] × Dᴰ.Hom[ g ][ liftω d , liftω d' ]
  _×Cᴰsmall_ .catᴰ .idᴰ = Cᴰ.idᴰ , Dᴰ.idᴰ
  _×Cᴰsmall_ .catᴰ ._⋆ᴰ_ (fᴰ , gᴰ) (fᴰ' , gᴰ') = fᴰ Cᴰ.⋆ᴰ fᴰ' , gᴰ Dᴰ.⋆ᴰ gᴰ'
  _×Cᴰsmall_ .catᴰ .⋆IdLᴰ _ =
    ΣPathP (
      ΣPathP ((C.⋆IdL _) , (D.⋆IdL _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdLᴰ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdLᴰ _)))
  _×Cᴰsmall_ .catᴰ .⋆IdRᴰ _ =
    ΣPathP (
      ΣPathP ((C.⋆IdR _) , (D.⋆IdR _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdRᴰ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdRᴰ _)))
  _×Cᴰsmall_ .catᴰ .⋆Assocᴰ _ _ _ =
    ΣPathP (
      ΣPathP ((C.⋆Assoc _ _ _) , (D.⋆Assoc _ _ _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆Assocᴰ _ _ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆Assocᴰ _ _ _)))
  _×Cᴰsmall_ .catᴰ .isSetHomᴰ = isSet× Cᴰ.isSetHomᴰ Dᴰ.isSetHomᴰ

module _
  {C : Category Cob CHom-ℓ}
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  (Dᴰ : Categoryᴰ C Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

    Δ : Functor C (C ×C C)
    Δ .Functor.F-ob = λ z → z , z
    Δ .Functor.F-hom = λ z → z , z
    Δ .Functor.F-id = refl
    Δ .Functor.F-seq = λ _ _ → refl

  _×ᴰ_ :
    Categoryᴰ C _ _
  _×ᴰ_ = reindexEq Δ (Cᴰ ×Cᴰ Dᴰ) Eq.refl (λ _ _ → Eq.refl)

module _
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
  {E : Category Eob EHom-ℓ}
  (F : Functor E C)
  (G : Functor E D)
  (Fᴰ : Section F Cᴰ) (Gᴰ : Section G Dᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  open Section
  introS-×Cᴰ : Section (F ,F G) (Cᴰ ×Cᴰ Dᴰ)
  introS-×Cᴰ .F-obᴰ = λ d → F-obᴰ Fᴰ d , F-obᴰ Gᴰ d
  introS-×Cᴰ .F-homᴰ = λ f → F-homᴰ Fᴰ f , F-homᴰ Gᴰ f
  introS-×Cᴰ .F-idᴰ =
    ΣPathP (ΣPathP ((Functor.F-id F) , (Functor.F-id G)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Fᴰ .F-idᴰ) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Gᴰ .F-idᴰ)))
  introS-×Cᴰ .F-seqᴰ fᴰ gᴰ =
    ΣPathP (ΣPathP ((Functor.F-seq F fᴰ gᴰ) , (Functor.F-seq G fᴰ gᴰ)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Fᴰ .F-seqᴰ fᴰ gᴰ) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Gᴰ .F-seqᴰ fᴰ gᴰ)))

module _
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
  {E : Category Eob EHom-ℓ}
  {Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ}
  (F : Functor E C)
  (G : Functor E D)
  (Fᴰ : Functorᴰ F Eᴰ Cᴰ) (Gᴰ : Functorᴰ G Eᴰ Dᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  open Functorᴰ
  introF-×Cᴰ : Functorᴰ (F ,F G) Eᴰ (Cᴰ ×Cᴰ Dᴰ)
  introF-×Cᴰ .Functorᴰ.F-obᴰ = λ z → Functorᴰ.F-obᴰ Fᴰ z , Functorᴰ.F-obᴰ Gᴰ z
  introF-×Cᴰ .Functorᴰ.F-homᴰ = λ fᴰ → Functorᴰ.F-homᴰ Fᴰ fᴰ , Functorᴰ.F-homᴰ Gᴰ fᴰ
  introF-×Cᴰ .Functorᴰ.F-idᴰ =
    ΣPathP (ΣPathP ((Functor.F-id F) , (Functor.F-id G)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Fᴰ .F-idᴰ) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Gᴰ .F-idᴰ)))
  introF-×Cᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ =
    ΣPathP (ΣPathP ((Functor.F-seq F _ _) , (Functor.F-seq G _ _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Fᴰ .F-seqᴰ fᴰ gᴰ) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Gᴰ .F-seqᴰ fᴰ gᴰ)))

module _
  {C : Category Cob CHom-ℓ}
  {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {Dᴰ : Categoryᴰ C Dobᴰ DHom-ℓᴰ}
  {E : Category Eob EHom-ℓ}
  (F : Functor E C)
  (Fᴰ : Section F Cᴰ) (Gᴰ : Section F Dᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  open Section
  introS : Section F (Cᴰ ×ᴰ Dᴰ)
  introS .F-obᴰ = λ d → F-obᴰ Fᴰ d , F-obᴰ Gᴰ d
  introS .F-homᴰ = λ f → F-homᴰ Fᴰ f , F-homᴰ Gᴰ f
  introS .F-idᴰ =
    ΣPathP (Functor.F-id F ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Fᴰ .F-idᴰ) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Gᴰ .F-idᴰ)))
  introS .F-seqᴰ fᴰ gᴰ =
    ΣPathP (Functor.F-seq F _ _ ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Fᴰ .F-seqᴰ fᴰ gᴰ) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Gᴰ .F-seqᴰ fᴰ gᴰ)))

module _
  {C : Category Cob CHom-ℓ}
  {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {Dᴰ : Categoryᴰ C Dobᴰ DHom-ℓᴰ}
  where
  private
    module C = CategoryNotation C
    module Cᴰ = CategoryᴰNotation Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
    module Cᴰ×Dᴰ = Categoryᴰ (Cᴰ ×ᴰ Dᴰ)
  module _
    {E : Category Eob EHom-ℓ}
    {Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ}
    {F : Functor E C}
    (Fᴰ : Functorᴰ F Eᴰ Cᴰ)
    (Gᴰ : Functorᴰ F Eᴰ Dᴰ)
    where
    open Functorᴰ
    private
      module Eᴰ = CategoryᴰNotation Eᴰ
    introF : Functorᴰ F Eᴰ (Cᴰ ×ᴰ Dᴰ)
    introF =
      recᴰ Eᴰ
        (introS _
          (TotalCat.elim Eᴰ Fᴰ)
          (TotalCat.elim Eᴰ Gᴰ))

  module _
    {Eᴰ : Categoryᴰ C Eobᴰ EHom-ℓᴰ}
    (Fᴰ : Functorⱽ Eᴰ Cᴰ)
    (Gᴰ : Functorⱽ Eᴰ Dᴰ)
    where
    open Functorᴰ
    private
      module Eᴰ = CategoryᴰNotation Eᴰ
    -- Don't actually need this definition if
    -- Functor has eta equality
    -- you can just use introF
    introFⱽ : Functorⱽ Eᴰ (Cᴰ ×ᴰ Dᴰ)
    introFⱽ =
      recᴰ Eᴰ
        (introS _
          (TotalCat.elim Eᴰ Fᴰ)
          (TotalCat.elim Eᴰ Gᴰ))

module _
  {C : SmallCategory ℓC ℓC'}
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  (Dᴰ : SmallCategoryᴰ C ℓDᴰ ℓDᴰ')
  where
  open SmallCategory
  open SmallCategoryᴰ
  private
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ
    module Dᴰ = SmallCategoryᴰ Dᴰ

    Δ : Functor C.cat ((C ×Csmall C) .cat)
    Δ .Functor.F-ob = λ z → liftω (z .Liftω.lowerω , z .Liftω.lowerω)
    Δ .Functor.F-hom = λ z → z , z
    Δ .Functor.F-id = refl
    Δ .Functor.F-seq = λ _ _ → refl

  -- The fiberwise product of displayed categories arises as the
  -- pullback --- that is, the reindexing --- of the displayed
  -- product of categories
  _×ᴰsmall_ : SmallCategoryᴰ C _ _
  _×ᴰsmall_ = smallcatᴰ _ (reindexEq Δ ((Cᴰ ×Cᴰsmall Dᴰ) .catᴰ) Eq.refl λ _ _ → Eq.refl)

  _×ᴰsmall'_ : SmallCategoryᴰ C _ _
  _×ᴰsmall'_ = smallcatᴰ _ (reindex' Δ ((Cᴰ ×Cᴰsmall Dᴰ) .catᴰ))

module _
  {C : Category Cob CHom-ℓ}{Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ}
  (Cᴰ : SmallFibersCategoryᴰ C Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ)
  {D : Category Dob DHom-ℓ} {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
    module D = CategoryNotation D
    module Dᴰ = Categoryᴰ Dᴰ

  _×CᴰSF_ : SmallFibersCategoryᴰ (C ×C D) _
            (λ (c , d) → Cobᴰ c × Dobᴰ d)
            _
  _×CᴰSF_ .Hom[_][_,_] (f , g) (liftω (c , d)) (liftω (c' , d')) =
    Cᴰ.Hom[ f ][ liftω c , liftω c' ] × Dᴰ.Hom[ g ][ liftω d , liftω d' ]
  _×CᴰSF_ .idᴰ = Cᴰ.idᴰ , Dᴰ.idᴰ
  _×CᴰSF_ ._⋆ᴰ_ (fᴰ , gᴰ) (fᴰ' , gᴰ') = fᴰ Cᴰ.⋆ᴰ fᴰ' , gᴰ Dᴰ.⋆ᴰ gᴰ'
  _×CᴰSF_ .⋆IdLᴰ _ =
    ΣPathP (
      ΣPathP ((C.⋆IdL _) , (D.⋆IdL _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdLᴰ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdLᴰ _)))
  _×CᴰSF_ .⋆IdRᴰ _ =
    ΣPathP (
      ΣPathP ((C.⋆IdR _) , (D.⋆IdR _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdRᴰ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdRᴰ _)))
  _×CᴰSF_ .⋆Assocᴰ _ _ _ =
    ΣPathP (
      ΣPathP ((C.⋆Assoc _ _ _) , (D.⋆Assoc _ _ _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆Assocᴰ _ _ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆Assocᴰ _ _ _)))
  _×CᴰSF_ .isSetHomᴰ = isSet× Cᴰ.isSetHomᴰ Dᴰ.isSetHomᴰ

module _
  {C : Category Cob CHom-ℓ}{Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ}
  (Cᴰ : SmallFibersCategoryᴰ C Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ)
  {D : Category Dob DHom-ℓ} {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = CategoryNotation C
    module Cᴰ = CategoryᴰNotation Cᴰ
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Cᴰ×Dᴰ = CategoryᴰNotation (Cᴰ ×CᴰSF Dᴰ)

  open Functor
  ×CᴰFiber→ProductOfFibers : ∀ {c} {d} →
    Functor Cᴰ×Dᴰ.v[ c , d ] (Cᴰ.v[ c ] ×C Dᴰ.v[ d ])
  ×CᴰFiber→ProductOfFibers .F-ob = λ z → liftω (z .Liftω.lowerω .fst) , liftω (z .Liftω.lowerω .snd)
  ×CᴰFiber→ProductOfFibers .F-hom = λ z → z
  ×CᴰFiber→ProductOfFibers .F-id = refl
  ×CᴰFiber→ProductOfFibers .F-seq _ _ = refl

  ProductOfFibers→×CᴰSFFiber :
    ∀ {c} {d} → Functor (Cᴰ.v[ c ] ×C Dᴰ.v[ d ]) Cᴰ×Dᴰ.v[ c , d ]
  ProductOfFibers→×CᴰSFFiber .F-ob = λ z → liftω (z .fst .Liftω.lowerω , z .snd .Liftω.lowerω)
  ProductOfFibers→×CᴰSFFiber .F-hom = λ z → z
  ProductOfFibers→×CᴰSFFiber .F-id = refl
  ProductOfFibers→×CᴰSFFiber .F-seq _ _ = refl

module _
  {D : Category Dob DHom-ℓ}
  {E : Category Eob EHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  {Eobᴰ-ℓ Eobᴰ EHom-ℓᴰ}
  (C : SmallCategory ℓC ℓC')
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  (Eᴰ : SmallFibersCategoryᴰ E Eobᴰ-ℓ Eobᴰ EHom-ℓᴰ)
  where
  private
    module C =  SmallCategory C
    module D =  CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
    module E =  CategoryNotation E
    module Eᴰ = CategoryᴰNotation Eᴰ
    module D×E =  CategoryNotation (D ×C E)
    module Dᴰ×ᴰEᴰ =  CategoryᴰNotation (Dᴰ ×CᴰSF Eᴰ)
    module FuncDᴰ = NatTransDefs C Dᴰ
    module NatTransDᴰ = FuncDᴰ.NatTrans
    module FuncEᴰ = NatTransDefs C Eᴰ
    module NatTransEᴰ = FuncEᴰ.NatTrans
    module FuncDᴰ×Eᴰ = NatTransDefs C (Dᴰ ×CᴰSF Eᴰ)
    module NatTransDᴰ×Eᴰ = FuncDᴰ×Eᴰ.NatTrans

  open Functorᴰ

  ,F-SFFunctorⱽ :
    Functorⱽ
      (FUNCTOR C Dᴰ ×Cᴰ FUNCTOR C Eᴰ)
      (FUNCTOR C (Dᴰ ×CᴰSF Eᴰ))
  ,F-SFFunctorⱽ .F-obᴰ (F , G) =
    ProductOfFibers→×CᴰSFFiber Dᴰ Eᴰ ∘F (F ,F G)
  ,F-SFFunctorⱽ .F-homᴰ fᴰ .NatTransDᴰ×Eᴰ.N-ob x = fᴰ .fst .NatTransDᴰ.N-ob x , fᴰ .snd .NatTransEᴰ.N-ob x
  ,F-SFFunctorⱽ .F-homᴰ {xᴰ = xᴰ}{yᴰ = yᴰ} (α , β) .NatTransDᴰ×Eᴰ.N-hom g =
       (ΣPathP (D×E.⋆IdL _ ∙ (sym $ D×E.⋆IdR _) ,
               ΣPathP (
                 (Dᴰ.rectify (Dᴰ.≡out $ NatTransDᴰ.N-hom α g)) ,
                 (Eᴰ.rectify (Eᴰ.≡out $ NatTransEᴰ.N-hom β g)))))
  ,F-SFFunctorⱽ .F-idᴰ =
    FuncDᴰ×Eᴰ.makeNatTransPath refl (λ _ → refl)
  ,F-SFFunctorⱽ .F-seqᴰ _ _ =
    FuncDᴰ×Eᴰ.makeNatTransPath refl (λ _ → refl)
