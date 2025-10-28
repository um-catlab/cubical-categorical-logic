{-
  The Tabulator of a profunctor specializes to the displayed category of elements of a presheaf.
-}

module Cubical.Categories.Displayed.Constructions.Graph.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Presheaf hiding (Elements)
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory as TotalCat

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Constructions.StructureOver

private
  variable
    ℓC ℓC' ℓD ℓD' ℓP ℓS : Level

open Category
open StructureOver
open Functor

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) where
  private
    module P = PresheafNotation P
  Elements : Categoryᴰ C ℓP ℓP
  Elements = StructureOver→Catᴰ Str where
    open StructureOver
    Str : StructureOver C _ _
    Str .ob[_] = P.p[_]
    -- this version lines up definitionally with fiber. See test-Elements below
    Str .Hom[_][_,_] f p q = (f P.⋆ q) ≡ p
    Str .idᴰ = P.⋆IdL _
    Str ._⋆ᴰ_ fy≡x gz≡y = P.⋆Assoc _ _ _ ∙ cong (_ P.⋆_) gz≡y ∙ fy≡x
    Str .isPropHomᴰ = P.isSetPsh _ _

  private
    module ∫Elements = Category (∫C Elements)
    test-Elements : ∀ x p y q
      → ∫Elements.Hom[ (x , p) , (y , q) ] ≡ fiber (P._⋆ q) p
    test-Elements x p y q = refl
