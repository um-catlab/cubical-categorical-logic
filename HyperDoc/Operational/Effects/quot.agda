module HyperDoc.Operational.Effects.quot where 

open import HyperDoc.Algebra.Algebra hiding (Term ; var)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Sum

record Sig : Set₁ where 
  constructor _◂_
  field 
    Op : Set 
    arity : Op → ℕ 

den : Sig → Set → Set 
den (Op ◂ arity) X = Σ[ op ∈ Op ] (Fin (arity op) → X)

TermF : Sig → Set → Set → Set 
TermF p X Y = X ⊎ den p Y

{-# NO_POSITIVITY_CHECK #-}
data μ (F : Set → Set) : Set where 
  inn : F (μ F) → μ F 

Term : Sig → Set → Set 
Term p X = μ (TermF p X)

module foo (S : Sig) where  
  open Sig S
  Trm = Term S

  var : {X : Set} → X → Trm X
  var {X} x = inn (inl x)

  op : {X : Set} → (o : Op) → (Fin (arity o) → Trm X) → Trm X
  op o args = inn (inr (o , args))


  record Eqn (X : Set) : Set where 
    field 
      lhs : Trm X 
      rhs : Trm X

  open Eqn

  record Eqns : Set₁ where 
    field 
      names : Set 
      eqns : {X : Set}(n : names) → Eqn X

  module bar (es : Eqns) where 
    open Eqns es
    
    data _≈_ {X : Set}: Trm X → Trm X → Set where

      eq : ∀ {l r}
        → (n : names) 
        → lhs (eqns n) ≈ rhs (eqns n)

      refl : ∀ {t} → t ≈ t

      sym  : ∀ {t u} → t ≈ u → u ≈ t

      trans : ∀ {t u v} → t ≈ u → u ≈ v → t ≈ v

      cong-op :
        ∀ {o ts us}
        → (∀ i → ts i ≈ us i)
        → op o ts ≈ op o us

    data Term/≈ (X : Set): Set where
      [_] : Trm X → Term/≈ X

      quot : ∀ {t u} → t ≈ u → [ t ] ≡ [ u ]

data Ops : Set where 
  e ⊗ : Ops 

MonSig : Sig 
MonSig .Sig.Op = Ops
MonSig .Sig.arity e = 0
MonSig .Sig.arity ⊗ = 2

open foo MonSig

data MonEqs : Set where 
  lunit runit assoc : MonEqs

MonEq : Eqns 
MonEq .foo.Eqns.names = MonEqs
MonEq .foo.Eqns.eqns lunit .foo.Eqn.lhs = op e λ ()
MonEq .foo.Eqns.eqns lunit .foo.Eqn.rhs = op ⊗ λ {zero → var {!   !}
                                                ; one → var {!   !}}
MonEq .foo.Eqns.eqns runit = {!   !}
MonEq .foo.Eqns.eqns assoc = {!   !}

open bar MonEq


