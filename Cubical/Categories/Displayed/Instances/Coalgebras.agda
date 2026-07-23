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

  COALGᴰ : Categoryᴰ (C ^op) ℓC' ℓC'
  COALGᴰ = ALGᴰ (F ^opF)

  COALG : Category (ℓ-max ℓC ℓC') (ℓ-max ℓC' ℓC')
  COALG = (∫C COALGᴰ) ^op

  -- An F-coalgebra: a carrier together with a structure map Γ → F Γ.
  Coalgebra : Type (ℓ-max ℓC ℓC')
  Coalgebra = Category.ob COALG

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
