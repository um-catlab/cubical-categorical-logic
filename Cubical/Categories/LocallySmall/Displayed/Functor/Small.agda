{-# OPTIONS --lossy-unification #-}
-- TODO: E and D

--   Cᴰ ---> Eᴰᴰ
--  /|      / |
-- C ---> Eᴰ  |
-- | 1 ---|> Dᴰ
-- |/     | /
-- 1 ---> D

--
module Cubical.Categories.LocallySmall.Displayed.Functor.Small where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
import Cubical.Categories.Functor as SmallFunctor
import Cubical.Categories.Displayed.Functor as SmallFunctorᴰ

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Instances.Unit
open import Cubical.Categories.LocallySmall.Instances.Functor.Small
import Cubical.Categories.LocallySmall.Functor.Base as LocallySmallF
open import Cubical.Categories.LocallySmall.Instances.Indiscrete
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor.Small

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.SmallDisplayedFibers
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
import Cubical.Categories.LocallySmall.Displayed.Functor.Base as LocallySmallFᴰ
import Cubical.Categories.LocallySmall.Displayed.Functor.Properties as LocallySmallFᴰ
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base

open Category
open Categoryᴰ
open Functor

open Liftω
open Σω

record Functorᴰ
  {C : SmallCategory ℓC ℓC'}
  {D : Category Dob DHom-ℓ}
  {Eob-ℓᴰ Eobᴰ EHom-ℓᴰ}
  {Eᴰ : SmallFibersCategoryᴰ D Eob-ℓᴰ Eobᴰ EHom-ℓᴰ}
  {d}
  (F : Functor C Eᴰ d)
  {ℓCᴰ ℓCᴰ'}
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  {Dobᴰ DHom-ℓᴰ}
  {Dᴰ : GloballySmallCategoryᴰ D Dobᴰ DHom-ℓᴰ}
  {Eᴰᴰ-ℓ Eobᴰᴰ EHom-ℓᴰᴰ}
  (Eᴰᴰ : SmallFibersᴰCategoryᴰ Dᴰ Eᴰ Eᴰᴰ-ℓ Eobᴰᴰ EHom-ℓᴰᴰ)
  (dᴰ : Dobᴰ d)
  : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
                (ℓ-max (EHom-ℓᴰᴰ d d dᴰ dᴰ) (Eᴰᴰ-ℓ d dᴰ)))
  where
  no-eta-equality
  constructor functorᴰ
  private
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Eᴰ = CategoryᴰNotation Eᴰ
    module Eᴰᴰ = CategoryᴰNotation Eᴰᴰ using (Hom[_][_,_]; _≡[_]_; idᴰ; _⋆ᴰ_; rectify)
    module F = Functor F

  field
    F-obᴰ : ∀ {c} (cᴰ : Cᴰ.obᴰ c) → Eobᴰᴰ (d , (dᴰ , (liftω (F.F-ob c))))
    F-homᴰ : ∀ {c c' cᴰ cᴰ'}{f : C.Hom[ liftω c , liftω c' ]} (fᴰ : Cᴰ.Hom[ f ][ liftω cᴰ , liftω cᴰ' ])
      → Eᴰᴰ.Hom[ D.id , Dᴰ.idᴰ , F.F-hom f ][ liftω (F-obᴰ cᴰ) , liftω (F-obᴰ cᴰ') ]
    F-idᴰ : ∀ {c} {cᴰ : Cᴰ.obᴰ c} →
      F-homᴰ (Cᴰ.idᴰ {xᴰ = liftω cᴰ})
        Eᴰᴰ.≡[ ΣPathP (refl , (ΣPathP (refl , F.F-id))) ]
      Eᴰᴰ.idᴰ
    F-seqᴰ : ∀ {c c' c'' cᴰ cᴰ' cᴰ''}
      {f : C.Hom[ liftω c , liftω c' ]}
      {g : C.Hom[ liftω c' , liftω c'' ]}
      (fᴰ : Cᴰ.Hom[ f ][ liftω cᴰ , liftω cᴰ' ])
      (gᴰ : Cᴰ.Hom[ g ][ liftω cᴰ' , liftω cᴰ'' ])
      → F-homᴰ (fᴰ Cᴰ.⋆ᴰ gᴰ)
          Eᴰᴰ.≡[ ΣPathP ((sym $ D.⋆IdL D.id) , ΣPathP (Dᴰ.rectify-out (sym $ Dᴰ.⋆IdLᴰ Dᴰ.idᴰ) , F.F-seq f g)) ]
        (F-homᴰ fᴰ Eᴰᴰ.⋆ᴰ F-homᴰ gᴰ)

  ∫F : Functor (SmallCategoryᴰ.∫Csmall Cᴰ) (∫Cᴰ D Dᴰ Eᴰ Eᴰᴰ) (d , dᴰ)
  ∫F .F-ob (c , cᴰ) = (F.F-ob c) , (F-obᴰ cᴰ)
  ∫F .F-hom (f , fᴰ) = (F.F-hom f) , (F-homᴰ fᴰ)
  ∫F .F-id = ΣPathP (F.F-id , F-idᴰ)
  ∫F .F-seq (f , fᴰ) (g , gᴰ) = ΣPathP (Eᴰ.rectify (F.F-seq f g) , (Eᴰᴰ.rectify $ F-seqᴰ fᴰ gᴰ))

-- TODO: NatTransᴰ, FUNCTORᴰ, Bifunctorᴰ, HOMᴰ
-- HOMᴰ : Bifunctorᴰ Cᴰ (Cᴰ ^opsmallfib) SETᴰ (liftω ? , ?)
