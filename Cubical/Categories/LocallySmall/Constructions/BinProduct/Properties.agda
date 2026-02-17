module Cubical.Categories.LocallySmall.Constructions.BinProduct.Properties where

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
-- open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Constructions.BinProduct.Base

open Category
open Σω
open Functor

module _
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  {E : Category Eob EHom-ℓ}
  where
  _,F_ : Functor C D → Functor C E → Functor C (D ×C E)
  (F ,F G) .F-ob = λ z → F-ob F z , F-ob G z
  (F ,F G) .F-hom = λ z → F-hom F z , F-hom G z
  (F ,F G) .F-id = ≡-× (F-id F) (F-id G)
  (F ,F G) .F-seq _ _ = ≡-× (F-seq F _ _) (F-seq G _ _)

module _
  {Bob BHom-ℓ}
  {B : Category Bob BHom-ℓ}
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  {E : Category Eob EHom-ℓ}
  where
  _×F_ : Functor B D → Functor C E → Functor (B ×C C) (D ×C E)
  F ×F G = (F ∘F π₁ _ _) ,F (G ∘F π₂ _ _)
