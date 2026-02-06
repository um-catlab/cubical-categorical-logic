module HyperDoc.AsDisplayed where 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Category 
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Posets.Base

open import Cubical.Categories.Displayed.Base

open import HyperDoc.Syntax

open Categoryᴰ

module convert 
  {ℓ ℓ' ℓP ℓP' : Level}{C : Category ℓ ℓ'}
  (F : Functor (C ^op) (POSET ℓP ℓP')) where 

  open HDSyntax F  

  Cᴰ : Categoryᴰ C ℓP ℓP' 
  ob[ Cᴰ ] = F∣_∣
  Cᴰ .Hom[_][_,_] {x}{y} f Fx Fy = x ◂ Fx ≤ f* f  Fy
  Cᴰ .idᴰ = eqTo≤  (sym f*id)
  Cᴰ ._⋆ᴰ_ {f = f} {g} = seq* f g
  Cᴰ .⋆IdLᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆IdRᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆Assocᴰ _ _ _ = toPathP (isProp≤ _ _)
  Cᴰ .isSetHomᴰ = isProp→isSet isProp≤ 