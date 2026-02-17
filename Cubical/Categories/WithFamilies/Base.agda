{-

  Categories with families are a model of the
  judgmental structure of simply typed lambda calculus.
  TODO: citation

-}
module Cubical.Categories.WithFamilies.Base where


open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions

open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Instances.Terminal

open Category
open NatTrans

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level
CwF : (ℓC ℓC' ℓT ℓT' : Level) → Type _
CwF ℓC ℓC' ℓT ℓT' =
  Σ[ C ∈ Category ℓC ℓC' ]
  Σ[ Ty ∈ Presheaf C ℓT ]
  Σ[ Tm ∈ Presheafᴰ Ty (Unitᴰ C) ℓT' ]
  Terminal C
  × (∀ Γ A → UniversalElement C (Comprehension Ty Tm Γ A))
