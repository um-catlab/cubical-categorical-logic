module Cubical.Categories.Displayed.Constructions.HomPropertyOver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.StructureOver

private
  variable
    ℓC ℓC' ℓP : Level

open Category

module _
  (C : Category ℓC ℓC') (P : ∀ {x y} → C [ x , y ] → Type ℓP)
  (Pprop : ∀ {x y} (f : C [ x , y ]) → isProp (P f))
  (Pid : ∀ {x} → P (id C {x}))
  (Pcomp : ∀ {x y z} (f : C [ x , y ]) (g : C [ y , z ]) → P f → P g → P (_⋆_ C f g))
  where

  HomPropertyOver : Categoryᴰ C ℓ-zero ℓP
  HomPropertyOver = StructureOver→Catᴰ struct where
    open StructureOver
    struct : StructureOver C ℓ-zero ℓP
    struct .ob[_] _ = Unit
    struct .Hom[_][_,_] f _ _ = P f
    struct .idᴰ = Pid
    struct ._⋆ᴰ_ = Pcomp _ _
    struct .isPropHomᴰ = Pprop _

module examples where
  module _
    (C : Category ℓC ℓC')
    where

    open import Cubical.Categories.Isomorphism
    open import Cubical.Categories.Constructions.TotalCategory

    open Category C

    -- Given as an example of a wide subcategory on nlab:
    -- https://ncatlab.org/nlab/show/core+groupoid
    Coreᴰ : Categoryᴰ C ℓ-zero ℓC'
    Coreᴰ =
      HomPropertyOver
      C (isIso C) isPropIsIso (idCatIso .snd)
      λ f g isIsof isIsog → compIso (g , isIsog) (f , isIsof) .snd 

    Core : Category ℓC ℓC'
    Core = ∫C Coreᴰ

    private
      module Core = Category Core

    morCore→isIso : ∀ {x y} (f : Core [ x , y ]) → isIso C (f .fst)
    morCore→isIso f = f .snd
