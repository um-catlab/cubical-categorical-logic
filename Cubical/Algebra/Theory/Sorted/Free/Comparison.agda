-- Three presentations of the free model, side by side.  Two are used
-- in this library; the third is the one you write first, and it has no
-- recursor.  The whole difference is how substitution is handled.
--
--                    naive           bind            closing
--                    (this file)     (Free/Bind)     (Free/Closing)
-- --------------------------------------------------------------------
--  substitution      derived fold    constructor     constructor
--                    `TmRec nnode`   `⟦_⟧_`          `clo`
--  at which contexts  --             any `Type ℓv`   `σeq .vars e`
--  equation endpoints stuck `TmRec`  constructors    constructors
--  recursor          NONE            `rec`           `rec`
--  carrier level     `ℓClosing`      `ℓFree`         `ℓClosing`
--
-- `⟦_⟧_` costs one universe because it quantifies over an arbitrary
-- context `{W : Type ℓv}`.  `clo` quantifies over `e : σeq .eqns` and
-- reuses the *given* type `σeq .vars e`, so it costs nothing.
--
-- Note the naive presentation sits at `ℓClosing` as well: the universe
-- bump was never its problem.  Its problem is `rec`.
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

-- `ℓFree` is `ℓClosing` plus the bump, on the nose.
module _ (ℓS ℓ ℓ' ℓ'' ℓv : Level) where
  ℓFree≡ : Ex.ℓFree ℓS ℓ ℓ' ℓ'' ℓv
           ≡ ℓ-max (Clo.ℓClosing ℓS ℓ ℓ' ℓ'' ℓv) (ℓ-suc ℓv)
  ℓFree≡ = refl

-- The naive presentation.  There is no substitution in the syntax at
-- all: the equations are imposed on the derived fold `TmRec _ nnode`.
-- Constructors are prefixed `n` so they never clash with `Tm`'s
-- `var`/`node`, `Ex.FreeModel`'s `gen`/`opF`, or `Clo.FreeModel`'s.
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

    -- The algebra structure is the constructor itself, and so is the
    -- `EQNSᴰ` obligation -- no three-step path through substitution
    -- laws, because that is how the equations were stated.
    NaiveOps : Ops {σ = σ} (NaiveFree V vs)
    NaiveOps = nnode

    NaiveEqns : (e : σeq .eqns)
      (ρ : (w : σeq .vars e) → NaiveFree V vs (σeq .varSort e w))
      → TmRec (NaiveFree V vs) NaiveOps ρ (σeq .lhs e)
        ≡ TmRec (NaiveFree V vs) NaiveOps ρ (σeq .rhs e)
    NaiveEqns = neqn

    -- `⊥`/`Bool` arities have no definitional η, so a named builder's
    -- selector is never syntactically `TmRec`'s.  Same bridge as in
    -- the other two files.
    opCong : (o : σ .ops)
      {g h : (a : σ .arities o) → NaiveFree V vs (σ .sortOf o a)}
      → ((a : σ .arities o) → g a ≡ h a)
      → Path (NaiveFree V vs (σ .resultSort o)) (nnode o g) (nnode o h)
    opCong o p i = nnode o (λ a → p a i)

  NaiveOb : (V : Type ℓv) (vs : V → S) → Category.ob (MOD σeq ℓN)
  NaiveOb V vs = (λ s → NaiveFree V vs s , ntrunc) , NaiveOps , NaiveEqns

  NaiveGen : (V : Type ℓv) (vs : V → S) (v : V) → NaiveFree V vs (vs v)
  NaiveGen V vs = nvar

  -- ------------------------------------------------------------------
  -- Where the recursor fails
  -- ------------------------------------------------------------------
  --
  -- Fix a model `(X , α , sat)`.  Two clauses are fine, the third is
  -- the whole story:
  --
  --   rec ρ (nvar v)      = ρ v
  --   rec ρ (nnode o ts)  = α o (λ a → rec ρ (ts a))
  --   rec ρ (neqn e ρ' i) = ?
  --
  -- `neqn`'s type fixes the hole's boundary:
  --
  --   i0 ↦ rec ρ (TmRec (NaiveFree V vs) nnode ρ' (lhs e))
  --   i1 ↦ rec ρ (TmRec (NaiveFree V vs) nnode ρ' (rhs e))
  --
  -- but all the model offers is `sat e`:
  --
  --   TmRec X α (rec ρ ∘ ρ') (lhs e) ≡ TmRec X α (rec ρ ∘ ρ') (rhs e)
  --
  -- `rec` applied outside a fold over the SYNTAX, against a fold over
  -- the MODEL.  Bridging them needs a fusion lemma, mutual with `rec`:
  --
  --   fuse : (M : Tm σ (σeq .vars e) (σeq .varSort e) s)
  --        → rec ρ (TmRec (NaiveFree V vs) nnode ρ' M)
  --          ≡ TmRec X α (rec ρ ∘ ρ') M
  --
  -- and its `node o ts` case unfolds the left-hand side to
  --
  --   α o (λ a → rec ρ (TmRec (NaiveFree V vs) nnode ρ' (ts a)))
  --                     ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  --
  -- so `rec` is called at a term the fold has just BUILT.  That term
  -- is a subterm of nothing in scope -- least of all of `neqn e ρ' i`,
  -- which is what `rec` matched on -- so the mutual pair has no
  -- decreasing measure.  Generalising `fuse` over an arbitrary `h`
  -- obeying `rec`'s `nnode` equation only makes the recursive call a
  -- partial application, which cannot be sized either.
  --
  -- A prop-valued motive does not rescue it.  The boundary above is a
  -- DEFINITIONAL demand, checked against those stuck `TmRec`s, and
  -- `isProp→PathP` discharges only propositional ones.
  --
  -- Both working presentations delete the stuck `TmRec` by making
  -- substitution a constructor.  The endpoints become `⟦ lhs e ⟧ ρ`
  -- and `clo e (lhs e) ρ` -- constructor applications `rec` matches on
  -- directly -- and `fuse` degenerates into computation.

  -- The asymmetry, made concrete: `NaiveOb` and `Clo.FreeOb` are
  -- objects of the SAME category, and only one direction exists.
  fromClosing : (V : Type ℓv) (vs : V → S)
    → ModHom σeq ℓN (Clo.FreeOb σeq V vs) (NaiveOb V vs)
  fromClosing V vs =
    Iso.inv (Clo.UPMod σeq V vs (NaiveOb V vs)) (NaiveGen V vs)

  fromClosingGen : (V : Type ℓv) (vs : V → S) (v : V)
    → fromClosing V vs .fst (vs v) (Clo.gen σeq V vs v) ≡ nvar v
  fromClosingGen V vs v = refl
