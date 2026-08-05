-- Models of an algebraic theory, displayed over SET
module Cubical.Algebra.Theory.Category where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.TotalCategory

open import Cubical.Algebra.Theory

private
  variable
    ℓ ℓ' ℓ'' ℓv ℓX : Level

open AlgTheorySig
open AlgTheoryEqns

module _ {σ : AlgTheorySig ℓ ℓ'} (σeq : AlgTheoryEqns σ ℓ'' ℓv) where

  MODᴰ : (ℓX : Level) → Categoryᴰ (SET ℓX) _ _
  MODᴰ ℓX .Categoryᴰ.ob[_] X = Alg σeq ⟨ X ⟩
  MODᴰ ℓX .Categoryᴰ.Hom[_][_,_] f B C = Homo σeq f B C
  MODᴰ ℓX .Categoryᴰ.idᴰ = idHomo σeq
  MODᴰ ℓX .Categoryᴰ._⋆ᴰ_ = _⋆Homo_ σeq
  MODᴰ ℓX .Categoryᴰ.⋆IdLᴰ fᴰ = refl
  MODᴰ ℓX .Categoryᴰ.⋆IdRᴰ fᴰ = refl
  MODᴰ ℓX .Categoryᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ = refl
  MODᴰ ℓX .Categoryᴰ.isSetHomᴰ {y = Y} =
    isProp→isSet (isPropHomo σeq (Y .snd))

  MOD : (ℓX : Level) → Category _ _
  MOD ℓX = ∫C (MODᴰ ℓX)

  -- a homomorphism of models; `Sorted.agda` has the sorted counterpart
  ModHom : (ℓX : Level) (M N : Category.ob (MOD ℓX)) → Type _
  ModHom ℓX M N = MOD ℓX [ M , N ]

  Forget : Functor (MOD ℓX) (SET ℓX)
  Forget = Fst

noEqns : (σ : AlgTheorySig ℓ ℓ') → AlgTheoryEqns σ ℓ-zero ℓ-zero
noEqns σ .eqns = ⊥
noEqns σ .vars ()
noEqns σ .lhs ()
noEqns σ .rhs ()

module _ (σ : AlgTheorySig ℓ ℓ') where
  ALGᴰ : (ℓX : Level) → Categoryᴰ (SET ℓX) _ _
  ALGᴰ = MODᴰ (noEqns σ)

  ALG : (ℓX : Level) → Category _ _
  ALG = MOD (noEqns σ)
