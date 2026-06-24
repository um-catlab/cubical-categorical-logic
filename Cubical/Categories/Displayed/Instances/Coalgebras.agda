module Cubical.Categories.Displayed.Instances.Coalgebras where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Algebras
open import Cubical.Categories.Instances.TotalCategory

private
  variable ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} (F : Functor C C) where

  CoAlgCatᴰ : Categoryᴰ (C ^op) ℓC' ℓC'
  CoAlgCatᴰ = AlgCatᴰ (F ^opF)

  CoalgebrasCategory : Category (ℓ-max ℓC ℓC') (ℓ-max ℓC' ℓC')
  CoalgebrasCategory = (∫C CoAlgCatᴰ) ^op

  TerminalCoalgebra : Type (ℓ-max ℓC ℓC')
  TerminalCoalgebra = InitialAlgebra (F ^opF)

module TerminalCoalgebraNotation {C : Category ℓC ℓC'} {F : Functor C C}
  (termCoalg : TerminalCoalgebra F) where

  open InitialAlgebraNotation {C = C ^op} {F = F ^opF} termCoalg public
    renaming ( μF to νF
             ; μF-carrier to νF-carrier
             ; in-alg to out-coalg
             ; fold to unfold
             ; fold-unique to unfold-unique )
