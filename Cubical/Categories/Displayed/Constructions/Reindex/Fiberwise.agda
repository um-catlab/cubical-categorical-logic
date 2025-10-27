module Cubical.Categories.Displayed.Constructions.Reindex.Fiberwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.Reindex.Base hiding (π)
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf.Base

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor

-- want to show in a nice way that if Dᴰ has fiberwise products, then
-- so does reindex F Dᴰ.

-- 
module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where
  -- Here's the proof in full. Given dᴰ , dᴰ' over F c
  -- F*Dᴰ [-][-, dᴰ ∧ dᴰ' ]
  -- ≅ reindPshᴰ F (Dᴰ [-][-, dᴰ ∧ dᴰ' ])
  -- ≅ reindPshᴰ F (Dᴰ [-][-, dᴰ ] × Dᴰ [-][-, dᴰ' ])
  -- ≅ reindPshᴰ F (Dᴰ [-][-, dᴰ ]) × reindPshᴰ F (Dᴰ [-][-, dᴰ' ])
  -- ≅ F*Dᴰ [-][-, dᴰ ]  × F*Dᴰ [-][-, dᴰ' ]
