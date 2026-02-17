module Cubical.Categories.LocallySmall.Functor.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

-- open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
-- open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation

open Functor

module _
  {C : Category Cob CHom-ℓ}
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  where
   private
     module Cᴰ = CategoryᴰNotation Cᴰ

   σ : (c : Cob) → Functor Cᴰ.v[ c ] Cᴰ.∫C
   σ c .F-ob = λ z → c , z
   σ c .F-hom = λ z → Category.id C , z
   σ c .F-id = sym $ Cᴰ.reind-filler _ _
   σ c .F-seq f g = sym $ Cᴰ.reind-filler _ _

module _ where
  open CategoryVariables
  _^opF  : Functor C D → Functor (C ^op) (D ^op)
  (F ^opF) .F-ob      = F .F-ob
  (F ^opF) .F-hom     = F .F-hom
  (F ^opF) .F-id      = F .F-id
  (F ^opF) .F-seq f g = F .F-seq g f
