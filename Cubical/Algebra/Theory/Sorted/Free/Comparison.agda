-- The design space for the free model of a many-sorted theory.
--
-- Three presentations of the term model, side by side.  Two of them
-- are used in this library; the third is recorded here because it is
-- the one one writes first, and it does not work.
--
--                      naive           bind-based        closing
--                      (this file)     (Free/Bind)       (Free/Closing)
-- ----------------------------------------------------------------------
--  `node` primitive    yes (`nnode`)   yes (`opF`)       yes (`node`)
--  subst primitive     no              yes (`⟦_⟧_`)      yes (`clo`)
--  subst contexts      --              any `W : Type ℓv` `σeq .vars e`
--  equations stated    derived fold    primitive subst   primitive subst
--    through           `TmRec nnode`   `⟦ lhs e ⟧ ρ`     `clo e (lhs e) ρ`
--  `EQNSᴰ` obligation  the constructor 3-step path       3-step path
--    for the model     `neqn` itself   (`FreeEqns`)      (`FreeEqns`)
--  recursor            NONE            `rec`, `recUniq`  `rec`, `recUniq`
--  universal property  NONE            `UPMod`           `UPMod`
--  prop eliminator     NONE            --                `Displayed/Elim`
--  carrier level       `ℓClosing`      `ℓFree`           `ℓClosing`
--  ℓ' (arities) vs     independent     independent       independent
--    ℓv (variables)
--  generator ctx `V`   `Type ℓv`       `Type ℓv`         `Type ℓv`
--
--    ℓFree    ℓS ℓ ℓ' ℓ'' ℓv = ℓS ⊔ ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓ-suc ℓv
--    ℓClosing ℓS ℓ ℓ' ℓ'' ℓv = ℓS ⊔ ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓv
--
-- The `ℓ-suc ℓv` is bought by `⟦_⟧_`'s `{W : Type ℓv}`: the bind-based
-- syntax quantifies over an arbitrary variable context, so it must
-- live one universe above the one those contexts inhabit.  `clo`
-- quantifies only over `e : σeq .eqns`, whose context `σeq .vars e` is
-- a *given* type, so nothing is quantified over `Type ℓv` and the
-- level does not move.  Both bind the generator context `V` to `Type
-- ℓv`, the level of the equations' variables; the arity level `ℓ'` is
-- free of `ℓv` in all three.
--
-- Both working presentations are live, for a practical reason:
--   * `Cubical.Algebra.Theory.Sorted.Free.Bind`'s `FreeModel` carries the `MOD`
--     tower's `FreeOb`/`UPMod`/`InitialMOD`, and is what
--     `Sorted/Presheaf/Free.agda` builds its free presheaf of models
--     on.
--   * `Cubical.Algebra.Theory.Sorted.Free.Closing`'s `FreeModel` is what
--     `Sorted/Displayed/Elim.agda` eliminates over: the displayed
--     eliminator needs the recursor at a carrier level that is not
--     forced up by `ℓ-suc`.
--
-- What the naive presentation does NOT have, and why (recorded, not
-- re-attempted here):
--
-- (1) No recursor into an arbitrary model.  For
--       rec : NaiveFree V vs s → X s
--     the `neqn e ρ i` clause must inhabit a path between
--     `rec (TmRec (NaiveFree V vs) nnode ρ (σeq .lhs e))` and the same
--     at `rhs e`, whereas the model's `sat e` supplies a path between
--     `TmRec X α (λ w → rec (ρ w)) (σeq .lhs e)` and the same at
--     `rhs e`.  The bridge is a fusion lemma
--       fuse : (M : Tm σ (σeq .vars e) (σeq .varSort e) s)
--            → rec (TmRec (NaiveFree V vs) nnode ρ M)
--              ≡ TmRec X α (λ w → rec (ρ w)) M
--     whose `node` case calls `rec` at
--     `nnode o (λ a → TmRec (NaiveFree V vs) nnode ρ (ts a))`, a term
--     the fold has just built and which is a structural subterm of
--     nothing in scope.  So `rec` and `fuse`, which must be mutual,
--     admit no decreasing measure.
--
-- (2) Generalising the fusion lemma over an arbitrary `h` satisfying
--     `rec`'s `nnode` equation only relocates the problem: the
--     recursive call becomes a partial application, which the
--     termination checker cannot size either.
--
-- (3) Not even the prop-valued eliminator survives.  One would hope to
--     discharge the `neqn e ρ i` clause by `isProp→PathP` and never
--     look at the endpoints.  But the clause's boundary is a
--     *definitional* demand: Agda checks the supplied path against the
--     values the other clauses give at `neqn e ρ i0` and `neqn e ρ i1`,
--     and those are `TmRec (NaiveFree V vs) nnode ρ (σeq .lhs e)` and
--     `... (σeq .rhs e)`, stuck applications of `TmRec` on which no
--     clause of the eliminator computes.  A propositional motive
--     cannot absorb a definitional obligation.
--
-- The two working presentations differ from the naive one exactly by
-- making substitution a constructor, so that `eqn`'s endpoints are
-- constructor applications and the matching `rec` clause is available
-- by pattern matching.  `clo` takes the minimum that achieves this:
-- only the contexts `σeq .vars e` that the equations actually need.
--
-- Note that `NaiveFree` sits at `ℓClosing`, the *same* level as the
-- closing presentation.  The universe bump was never the naive
-- presentation's problem; its problem is purely the recursor.
module Cubical.Algebra.Theory.Sorted.Free.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category using (Category)

open import Cubical.Algebra.Theory.Sorted
  using (SortedSig; SortedEqns; Tm; Ops; TmRec; MOD; ModHom)

import Cubical.Algebra.Theory.Sorted.Free.Bind as Ex
import Cubical.Algebra.Theory.Sorted.Free.Closing as Clo

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv : Level

open SortedSig
open SortedEqns

-- The two levels, related.  `ℓFree` is `ℓClosing` with the bump.
module _ (ℓS ℓ ℓ' ℓ'' ℓv : Level) where
  ℓFree≡ : Ex.ℓFree ℓS ℓ ℓ' ℓ'' ℓv
           ≡ ℓ-max (Clo.ℓClosing ℓS ℓ ℓ' ℓ'' ℓv) (ℓ-suc ℓv)
  ℓFree≡ = refl

-- Presentation (1): the naive one.  `nnode` is a constructor and the
-- equations are imposed on the *derived* fold `TmRec _ nnode`, with no
-- substitution in the syntax at all.  Constructor names are prefixed
-- so that they never clash with `Tm`'s `var`/`node`, with
-- `Ex.FreeModel`'s `gen`/`opF` or with `Clo.FreeModel`'s `var`/`node`.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' ℓv) where

  private
    ℓN = Clo.ℓClosing ℓS ℓ ℓ' ℓ'' ℓv

  data NaiveFree (V : Type ℓv) (vs : V → S) : S → Type ℓN where
    nvar : (v : V) → NaiveFree V vs (vs v)
    nnode : (o : σ .ops)
      → ((a : σ .arities o) → NaiveFree V vs (σ .sortOf o a))
      → NaiveFree V vs (σ .resultSort o)
    neqn : (e : σeq .eqns)
      (ρ : (w : σeq .vars e) → NaiveFree V vs (σeq .varSort e w))
      → TmRec (NaiveFree V vs) nnode ρ (σeq .lhs e)
        ≡ TmRec (NaiveFree V vs) nnode ρ (σeq .rhs e)
    ntrunc : {s : S} → isSet (NaiveFree V vs s)

  module _ {V : Type ℓv} {vs : V → S} where

    -- Everything that genuinely works.  The algebra structure is the
    -- constructor `nnode`, and -- unlike in either working
    -- presentation, where `FreeEqns` is a three-step path through the
    -- substitution laws -- the `EQNSᴰ` obligation is the constructor
    -- `neqn` on the nose, because that is exactly how it was stated.
    NaiveOps : Ops {σ = σ} (NaiveFree V vs)
    NaiveOps = nnode

    NaiveEqns : (e : σeq .eqns)
      (ρ : (w : σeq .vars e) → NaiveFree V vs (σeq .varSort e w))
      → TmRec (NaiveFree V vs) NaiveOps ρ (σeq .lhs e)
        ≡ TmRec (NaiveFree V vs) NaiveOps ρ (σeq .rhs e)
    NaiveEqns = neqn

    -- `⊥`/`Bool` arities have no definitional η, so the selector a
    -- named term builder produces is never syntactically the one
    -- `TmRec` produces; this is the bridge, as in the other two files.
    opCong : (o : σ .ops)
      {g h : (a : σ .arities o) → NaiveFree V vs (σ .sortOf o a)}
      → ((a : σ .arities o) → g a ≡ h a)
      → Path (NaiveFree V vs (σ .resultSort o)) (nnode o g) (nnode o h)
    opCong o p i = nnode o (λ a → p a i)

  -- So the naive syntax *is* an object of `MOD` at `ℓClosing`: nothing
  -- above required a recursor.  What is missing is every map out of
  -- it.
  NaiveOb : (V : Type ℓv) (vs : V → S) → Category.ob (MOD σeq ℓN)
  NaiveOb V vs = (λ s → NaiveFree V vs s , ntrunc) , NaiveOps , NaiveEqns

  NaiveGen : (V : Type ℓv) (vs : V → S) (v : V) → NaiveFree V vs (vs v)
  NaiveGen V vs = nvar

  -- The asymmetry, made concrete.  `NaiveOb` and `Clo.FreeOb` are
  -- objects of the *same* category `MOD σeq ℓClosing` -- no lifting,
  -- no level reconciliation -- and the closing presentation's
  -- universal property hands over the comparison map for free.  The
  -- converse map is precisely what a recursor for `NaiveFree` would
  -- provide, and by (1)-(3) above there is none, so this square is
  -- one-directional by construction.
  fromClosing : (V : Type ℓv) (vs : V → S)
    → ModHom σeq ℓN (Clo.FreeOb σeq V vs) (NaiveOb V vs)
  fromClosing V vs =
    Iso.inv (Clo.UPMod σeq V vs (NaiveOb V vs)) (NaiveGen V vs)

  -- and it does send generators to generators, by `UPMod .Iso.sec`
  fromClosingGen : (V : Type ℓv) (vs : V → S) (v : V)
    → fromClosing V vs .fst (vs v) (Clo.gen σeq V vs v) ≡ nvar v
  fromClosingGen V vs v = refl
