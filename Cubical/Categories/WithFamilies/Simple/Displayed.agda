{-

  A displayed SCwF is an abstract notion of "logical family" over a SCwF

-}
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
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory
-- open import Cubical.Categories.Constructions.TotalCategory.Limits
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
open import Cubical.Categories.Displayed.Limits.Terminal renaming (preservesTerminal to secPreservesTerminal)
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Section
import Cubical.Categories.Displayed.Presheaf.CartesianLift as Presheafᴰ

private
  variable
    ℓC ℓC' ℓT ℓT' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level

open UniversalElement
open UniversalElementᴰ
open Bifunctorᴰ
open isIsoOver
open Iso

SCwFᴰ : (C : SCwF ℓC ℓC' ℓT ℓT') → (ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level) → Type _
SCwFᴰ (C , Ty , Tm , term , comprehension) ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' =
  Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
  let module Cᴰ = Categoryᴰ Cᴰ in
  Σ[ Tyᴰ ∈ (Ty → Type ℓTᴰ) ]
  Σ[ Tmᴰ ∈ (∀ {A} (Aᴰ : Tyᴰ A) → Presheafᴰ (Tm A) Cᴰ ℓTᴰ') ]
  Terminalᴰ Cᴰ term ×
  (∀ {A} (Aᴰ : Tyᴰ A) → LocallyRepresentableᴰ (_ , comprehension A) (Tmᴰ Aᴰ))

SCwFⱽ : (C : SCwF ℓC ℓC' ℓT ℓT') → (ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level) → Type _
SCwFⱽ (C , Ty , Tm , term , comprehension) ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' =
  Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
  let module Cᴰ = Categoryᴰ Cᴰ in
  Σ[ Tyᴰ ∈ (Ty → Type ℓTᴰ) ]
  Σ[ Tmᴰ ∈ (∀ {A} (Aᴰ : Tyᴰ A) → Presheafᴰ (Tm A) Cᴰ ℓTᴰ') ]
  Terminalsⱽ Cᴰ ×
  isFibration Cᴰ ×
  BinProductsⱽ Cᴰ ×
  (∀ {A} (Aᴰ : Tyᴰ A) → Presheafᴰ.isFibration (Tmᴰ Aᴰ))

-- A (strict) section is a section that preserves the SCwF structure on the nose
module _ (C : SCwF ℓC ℓC' ℓT ℓT') ((Cᴰ , Tyᴰ , Tmᴰ , termᴰ , comprehensionᴰ) : SCwFᴰ C ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') where
  open Section
  StrictSection : Type _
  StrictSection =
    Σ[ F ∈ GlobalSection Cᴰ ]
    Σ[ F-ty ∈ (∀ A → Tyᴰ A) ]
    -- Takes a Tm A Γ to a Tmᴰ
    Σ[ F-tm ∈ (∀ A → PshSection F (Tmᴰ (F-ty A))) ]
    -- preserves terminal object
    strictlyPreservesTerminal F _ termᴰ
    × (∀ A → strictlyPreservesLocalRep (Tmᴰ (F-ty A) , comprehensionᴰ (F-ty A)) (F-tm A))

  -- A variant that weakly preserves the structure
  SCwFSection : Type _
  SCwFSection =
    Σ[ F ∈ GlobalSection Cᴰ ]
    Σ[ F-ty ∈ (∀ A → Tyᴰ A) ]
    Σ[ F-tm ∈ (∀ A → PshSection F (Tmᴰ (F-ty A))) ]
    secPreservesTerminal F (C .snd .snd .snd .fst)
    × (∀ A → preservesLocalRep (Tmᴰ (F-ty A) , comprehensionᴰ (F-ty A)) (F-tm A))

 -- TODO StrictSection → SCwFSection
