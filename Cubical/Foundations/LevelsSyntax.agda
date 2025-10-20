module Cubical.Foundations.LevelsSyntax where

open import Cubical.Foundations.Prelude
import Cubical.Data.List as List

-- I'm really sick of manually writing out the max
-- of a list of levels manually as a tree
ℓ-max' : List.List Level → Level
ℓ-max' = List.foldr ℓ-max ℓ-zero

⌈_⌉ℓ = ℓ-max'
infix 1 ⌈_⌉ℓ

module reexport where
  _,ℓ_ = List._∷_ {A = Level}
  infixr 5 _,ℓ_
  0ℓ = List.[] {A = Level}

open reexport public
