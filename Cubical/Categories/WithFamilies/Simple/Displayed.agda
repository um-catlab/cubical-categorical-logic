{-

  A displayed SCwF is an abstract notion of "logical family" over a SCwF

-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.WithFamilies.Simple.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory

open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More renaming (preservesTerminal to funcPreservesTerminal)
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.WithFamilies.Simple.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Terminal as Terminal
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
-- open import Cubical.Categories.Displayed.Presheaf.Section
open import Cubical.Categories.Displayed.Section

import Cubical.Categories.Displayed.Presheaf.CartesianLift as Presheafᴰ

private
  variable
    ℓC ℓC' ℓT ℓT' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level

open UniversalElement
open Bifunctorᴰ
open isIsoOver
open Iso

record SCwFᴰ (S : SCwF ℓC ℓC' ℓT ℓT') (ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level) : Type
  (ℓ-suc (ℓ-max ℓC $ ℓ-max ℓC' $ ℓ-max ℓT $ ℓ-max ℓT' $ ℓ-max ℓCᴰ $ ℓ-max ℓCᴰ' $ ℓ-max  ℓTᴰ $ ℓTᴰ')) where
  no-eta-equality
  open SCwF S
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    Tyᴰ : Ty → Type ℓTᴰ
    Tmᴰ : ∀ {A} (Aᴰ : Tyᴰ A) → Presheafᴰ (Tm A) Cᴰ ℓTᴰ'
    termᴰ : Terminalᴰ Cᴰ term
    comprehensionᴰ : ∀ {A} (Aᴰ : Tyᴰ A) → isLRᴰ (_ , comprehension A) (Tmᴰ Aᴰ)

  module Cᴰ = Fibers Cᴰ
  module Tmᴰ {A : Ty}{Aᴰ : Tyᴰ A} = PresheafᴰNotation Cᴰ (Tm A) (Tmᴰ Aᴰ)
  module termᴰ = UniversalElementᴰNotation Cᴰ _ _ {ue = term} termᴰ
  module comprehensionᴰ {Γ}{A}{Γᴰ : Cᴰ.ob[ Γ ]}{Aᴰ : Tyᴰ A} =
    UniversalElementᴰNotation _ _ _ (comprehensionᴰ Aᴰ Γᴰ)

SCwFⱽ : (S : SCwF ℓC ℓC' ℓT ℓT') (ℓCᴰ ℓCᴰ' : Level) → Type (ℓ-suc (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ'))
SCwFⱽ S = CartesianCategoryⱽ (SCwF.C S)

-- -- A (strict) section is a section that preserves the SCwF structure on the nose
-- module _ (S : SCwF ℓC ℓC' ℓT ℓT') (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') where
--   open SCwFᴰ Sᴰ
--   open Section

--   record StrictSection : Type (ℓ-max ℓTᴰ' $ ℓ-max ℓCᴰ' $ ℓ-max ℓCᴰ $ ℓ-max ℓT $ ℓ-max ℓC $ ℓ-max ℓT' $ ℓ-max ℓC' $ ℓTᴰ) where
--     no-eta-equality
--     field
--       F : GlobalSection Cᴰ
--       F-ty : ∀ A → Tyᴰ A
--       -- Takes a Tm A Γ to a Tmᴰ
--       F-tm : ∀ A → PshSection F (Tmᴰ (F-ty A))
--       -- preserves terminal object
--       F-term : strictlyPreservesTerminal F _ termᴰ
--       F-comp : ∀ A → strictlyPreservesLocalRep (Tmᴰ (F-ty A) , comprehensionᴰ (F-ty A)) (F-tm A)
