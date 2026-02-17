-- Define a subcagtegory of a given category C by filtering
-- out the morphisms that satisfy a given property.
-- This is made precise by defining a displayed category
-- whose displayed morphisms are proofs that the morphisms
-- in the original category satisfy the predicate
--
-- This construction is the equivalent to a wide subcategory of C
-- https://ncatlab.org/nlab/show/wide+subcategory
module Cubical.Categories.LocallySmall.Displayed.Constructions.HomPropertyOver where

open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
-- open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Category.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
-- open import Cubical.Categories.LocallySmall.Displayed.HLevels
open import Cubical.Categories.LocallySmall.Displayed.Constructions.StructureOver.Base


record HomPropertyOver (C : Category Cob CHom-ℓ) ℓH : Typeω where
  open Category C
  field
    Hom[_][-,-] : ∀ {x y} → Hom[ x , y ] → Type ℓH
    isPropHomᴰ : ∀ {x y} (f : Hom[ x , y ]) → isProp Hom[ f ][-,-]
    idᴰ : ∀ {x} → Hom[ id {x} ][-,-]
    _⋆ᴰ_ : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ])
      → Hom[ f ][-,-] → Hom[ g ][-,-] → Hom[ f ⋆ g ][-,-]

module _ {ℓH} {C : Category Cob CHom-ℓ} (Pᴰ : HomPropertyOver C ℓH) where
  open Category C
  open HomPropertyOver Pᴰ
  HomPropertyOver→Catᴰ : Categoryᴰ C _ _
  HomPropertyOver→Catᴰ = StructureOver→Catᴰ struct where
    struct : StructureOver C (λ _ → Liftω Unit) _
    struct .StructureOver.Hom[_][_,_] f _ _ = Hom[ f ][-,-]
    struct .StructureOver.idᴰ = idᴰ
    struct .StructureOver._⋆ᴰ_ = _ ⋆ᴰ _
    struct .StructureOver.isPropHomᴰ = isPropHomᴰ _
