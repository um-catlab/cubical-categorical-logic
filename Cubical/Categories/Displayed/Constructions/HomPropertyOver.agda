module Cubical.Categories.Displayed.Constructions.HomPropertyOver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.StructureOver

private
  variable
    ℓC ℓC' ℓP : Level

open Category

module _
  (C : Category ℓC ℓC') (P : ∀ {x y} → C [ x , y ] → Type ℓP)
  (isPropP : ∀ {x y} {f : C [ x , y ]} → isProp (P f))
  (idP : ∀ {x} → P (id C {x}))
  (compP : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]} → P f → P g → P (_⋆_ C f g))
  where

  HomPropertyOver : Categoryᴰ C ℓ-zero ℓP
  HomPropertyOver = StructureOver→Catᴰ struct where
    open StructureOver
    struct : StructureOver C ℓ-zero ℓP
    struct .ob[_] _ = Unit
    struct .Hom[_][_,_] f _ _ = P f
    struct .idᴰ = idP
    struct ._⋆ᴰ_ = compP
    struct .isPropHomᴰ = isPropP
