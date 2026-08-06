-- A worked binary logical relation, to check that the abstraction
-- theorem is usable and that its conclusion is not vacuous.
--
-- The theory is one constant and one binary operation, no equations.
-- `OrMod` interprets it as `(false , _or_)`, `AndMod` as
-- `(true , _and_)`, and the relation is `x ~ y iff x ≡ not y`: its
-- closure under the operations is exactly De Morgan.  The abstraction
-- theorem then says every closed term is interpreted by complementary
-- booleans, with no induction over the syntax.
module Cubical.Algebra.Theory.Sorted.Displayed.RelationExample where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool
open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category

open import Cubical.Algebra.Theory.Sorted
  using (SortedSig; SortedEqns; Ops; MOD)
open import Cubical.Algebra.Theory.Sorted.Closing
  using (FreeModel)
open import Cubical.Algebra.Theory.Sorted.Displayed.Relation

open SortedSig
open SortedEqns

data MOp : Type where
  one mul : MOp

MSig : SortedSig Unit ℓ-zero ℓ-zero
MSig .ops = MOp
MSig .arities one = ⊥* {ℓ-zero}
MSig .arities mul = Bool
MSig .sortOf _ _ = tt
MSig .resultSort _ = tt

MEqns : SortedEqns MSig ℓ-zero ℓ-zero
MEqns .eqns = ⊥* {ℓ-zero}
MEqns .eqnSort ()
MEqns .vars ()
MEqns .varSort ()
MEqns .lhs ()
MEqns .rhs ()

OrMod : Category.ob (MOD MEqns ℓ-zero)
OrMod = (λ _ → Bool , isSetBool) , α , λ ()
  where
    α : Ops {σ = MSig} (λ _ → Bool)
    α one _ = false
    α mul x = x true or x false

AndMod : Category.ob (MOD MEqns ℓ-zero)
AndMod = (λ _ → Bool , isSetBool) , β , λ ()
  where
    β : Ops {σ = MSig} (λ _ → Bool)
    β one _ = true
    β mul x = x true and x false

deMorgan : (a b : Bool) → (not a or not b) ≡ not (a and b)
deMorgan true b = refl
deMorgan false b = refl

-- x is related to y iff x = not y.  De Morgan is exactly the closure of
-- this relation under the operations.
NotRel : Rel MEqns OrMod AndMod ℓ-zero
NotRel = mkRel MEqns OrMod AndMod
  (propRel MEqns OrMod AndMod
    (λ _ x y → (x ≡ not y) , isSetBool _ _)
    clos)
  where
    clos : (o : MOp) (x y : MSig .arities o → Bool)
      → ((a : MSig .arities o) → x a ≡ not (y a))
      → OrMod .snd .fst o x ≡ not (AndMod .snd .fst o y)
    clos one x y p = refl
    clos mul x y p =
      cong₂ _or_ (p true) (p false) ∙ deMorgan (y true) (y false)

-- The payoff: every CLOSED term of the theory is sent by the two
-- interpretations to complementary booleans.
smoke : (t : FreeModel MEqns (⊥* {ℓ-zero}) (noVar MEqns) tt)
  → closedM MEqns OrMod AndMod NotRel t
    ≡ not (closedN MEqns OrMod AndMod NotRel t)
smoke = closedRelated MEqns OrMod AndMod NotRel tt
