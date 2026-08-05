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

-- The universal property is NOT available here: `rec` is not definable
-- by pattern matching.  The `eqn` clause needs the fusion lemma
--
--   rec (TmRec node ρ M) ≡ Alg.⟦ rec ∘ ρ ⟧Tm B M
--
-- whose `node` case calls `rec` on `TmRec node ρ (ts a)`, not a subterm
-- of `eqn e ρ i`.  Generalising the lemma over an arbitrary `h` with
-- `rec`'s `node` computation rule does not help either: passing `rec ρ`
-- as an argument is still a call of unknown size.  Both are rejected by
-- the termination checker.
--
-- So the two presentations trade off exactly against each other:
--
--   node as constructor  -- algebra structure free, eliminator blocked
--   [_] : Tm σ V → _     -- eliminator free, algebra structure needs
--                           choice to lift `arities op → Tm σ V / ~`
--
-- For finitary arities the second is the one that works, which is what
-- `Free/Signature` does with `Vec` arities.  For infinitary ones the
-- first needs a postulated QIIT with rewrite rules.
--
-- Neither horn is forced, though: `Cubical.Algebra.Theory.Free.Explicit`
-- carries the term in the constructor, which makes the recursion
-- structural and needs neither choice nor a quotient.
