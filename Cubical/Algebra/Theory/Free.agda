module Cubical.Algebra.Theory.Free where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Theory

private
  variable
    ℓ ℓ' ℓ'' ℓv ℓX : Level

open AlgTheorySig

module _ {σ : AlgTheorySig ℓ ℓ'} (σeq : AlgTheoryEqns σ ℓ'' ℓv) where
  private module E = AlgTheoryEqns σeq

  data FreeModel (V : Type ℓv)
    : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓv)) where
    var : V → FreeModel V
    node : (op : σ .ops) → (σ .arities op → FreeModel V) → FreeModel V
    eqn : (e : E.eqns) (ρ : E.vars e → FreeModel V)
      → TmRec node ρ (E.lhs e) ≡ TmRec node ρ (E.rhs e)
    trunc : isSet (FreeModel V)

  FreeAlg : (V : Type ℓv) → Alg σeq (FreeModel V)
  FreeAlg V .Alg.⟨_⟩⟦_⟧op = node
  FreeAlg V .Alg.⟦_⟧eqn = eqn

-- The algebra structure is immediate -- `node` and `eqn` are literally
-- the two fields -- but there is no recursor, and hence no universal
-- property and no initiality.
--
-- `rec` into an algebra `B` is not definable by pattern matching: its
-- `eqn` clause needs the fusion lemma
--
--   rec (TmRec node ρ M) ≡ Alg.⟦ rec ∘ ρ ⟧Tm B M
--
-- whose `node` case calls `rec` at `TmRec node ρ (ts a)`, which is not a
-- subterm of `eqn e ρ i`.  Generalising over an arbitrary `h` satisfying
-- `rec`'s `node` computation rule only relocates the problem: passing
-- `rec ρ` as an argument is still a call of unknown size.  The
-- termination checker rejects both.
--
-- Only the prop-valued eliminator survives, since a prop-valued motive
-- discharges the `eqn` case outright.
--
-- `Cubical.Algebra.Theory.Free.Explicit` carries the substituted term in
-- the constructor, which makes that recursion structural; it is the
-- presentation everything downstream is built on.
