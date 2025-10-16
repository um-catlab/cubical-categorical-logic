module Cubical.Categories.WithFamilies.Simple.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
-- open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

-- open import Cubical.HITs.GroupoidTruncation

-- open import Cubical.Data.Sigma
open import Cubical.Data.Quiver.Base
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.SumFin

open import Cubical.Categories.Category
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Properties
-- open import Cubical.Categories.Bifunctor
-- open import Cubical.Categories.Yoneda
-- open import Cubical.Categories.Functor
-- open import Cubical.Categories.Instances.Sets
-- open import Cubical.Categories.Instances.Discrete
-- open import Cubical.Categories.Limits.Terminal.More
-- open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Product
-- open import Cubical.Categories.Presheaf.Representable
-- open import Cubical.Categories.Presheaf.Representable.More
-- open import Cubical.Categories.Profunctor.General


private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓQ ℓQ' ℓ ℓ' : Level

open Category

module _ (base-ty : Type ℓ) where
  record SignatureOver ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      funsym : Type ℓ'
      dom : funsym → Σ[ n ∈ ℕ ] (Fin n → base-ty)
      cod : funsym → base-ty

Signature : ∀ ℓ ℓ' → Type _
Signature ℓ ℓ' = Σ[ base-ty ∈ Type ℓ ] SignatureOver base-ty ℓ'

module _ ((base-ty , function-symbols) : Signature ℓ ℓ') (S : SCwF ℓC ℓC' ℓT ℓT') where
  open SignatureOver function-symbols
  open SCwFNotation S

  record Interp : Typeω where
    field
      ↑ty_ : base-ty → Ty
    field
      ↑fun_ : (f : funsym) →
              PshHom
                (FinProdPsh (λ k → Tm (↑ty dom f .snd k)))
                (Tm (↑ty (cod f)))

record SCwFOver (sig : Signature ℓ ℓ') ℓC ℓC' ℓT ℓT' : Typeω where
  field
    S : SCwF ℓC ℓC' ℓT ℓT'
    interp : Interp sig S
