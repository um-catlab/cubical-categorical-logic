-- The free model presented with a closing substitution for the
-- equation endpoints only.
module Cubical.Algebra.Theory.Free.Closing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Initial

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Category

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
    clo : (e : E.eqns) → Tm σ (E.vars e) → (E.vars e → FreeModel V)
      → FreeModel V
    cloVar : (e : E.eqns) (w : E.vars e) (ρ : E.vars e → FreeModel V)
      → clo e (var w) ρ ≡ ρ w
    cloNode : (e : E.eqns) (op : σ .ops)
      (ts : σ .arities op → Tm σ (E.vars e))
      (ρ : E.vars e → FreeModel V)
      → clo e (node op ts) ρ ≡ node op (λ a → clo e (ts a) ρ)
    eqn : (e : E.eqns) (ρ : E.vars e → FreeModel V)
      → clo e (E.lhs e) ρ ≡ clo e (E.rhs e) ρ
    trunc : isSet (FreeModel V)

  -- `clo` is determined by induction on the term: `cloVar`/`cloNode`
  -- say it agrees with the external recursor `TmRec node`.
  cloTmRec : {V : Type ℓv} (e : E.eqns) (ρ : E.vars e → FreeModel V)
    (M : Tm σ (E.vars e)) → clo e M ρ ≡ TmRec node ρ M
  cloTmRec e ρ (var w) = cloVar e w ρ
  cloTmRec e ρ (node op ts) =
    cloNode e op ts ρ
    ∙ (λ i → node op (λ a → cloTmRec e ρ (ts a) i))

  FreeAlg : (V : Type ℓv) → Alg σeq (FreeModel V)
  FreeAlg V .Alg.⟨_⟩⟦_⟧op = node
  FreeAlg V .Alg.⟦_⟧eqn e ρ =
    sym (cloTmRec e ρ (E.lhs e)) ∙ eqn e ρ ∙ cloTmRec e ρ (E.rhs e)

  Homo-Tm : {ℓY ℓZ : Level} {Y : Type ℓY} {Z : Type ℓZ} {g : Y → Z}
    {C : Alg σeq Y} {D : Alg σeq Z} (ϕ : Homo σeq g C D)
    {W : Type ℓv} (ρ : W → Y) (M : Tm σ W)
    → g (Alg.⟦_⟧Tm C ρ M) ≡ Alg.⟦_⟧Tm D (λ w → g (ρ w)) M
  Homo-Tm ϕ ρ (var w) = refl
  Homo-Tm {D = D} ϕ ρ (node op ts) =
    Homo.op-hom' ϕ op _
    ∙ (λ i → Alg.⟨_⟩⟦_⟧op D op (λ a → Homo-Tm ϕ ρ (ts a) i))

  module _ {X : Type ℓX} (isSetX : isSet X) (B : Alg σeq X) where
    private module B = Alg B

    rec : {V : Type ℓv} (ρ : V → X) → FreeModel V → X
    rec ρ (var v) = ρ v
    rec ρ (node op ts) = B.⟨ op ⟩⟦ (λ a → rec ρ (ts a)) ⟧op
    rec ρ (clo e M ρ') = B.⟦ (λ w → rec ρ (ρ' w)) ⟧Tm M
    rec ρ (cloVar e w ρ' i) = rec ρ (ρ' w)
    rec ρ (cloNode e op ts ρ' i) =
      B.⟨ op ⟩⟦ (λ a → B.⟦ (λ w → rec ρ (ρ' w)) ⟧Tm (ts a)) ⟧op
    rec ρ (eqn e ρ' i) = B.⟦ e ⟧eqn (λ w → rec ρ (ρ' w)) i
    rec ρ (trunc x y p q i j) =
      isSetX (rec ρ x) (rec ρ y) (cong (rec ρ) p) (cong (rec ρ) q) i j

    recβ : {V : Type ℓv} (ρ : V → X) (v : V) → rec ρ (var v) ≡ ρ v
    recβ ρ v = refl

    recHomo : {V : Type ℓv} (ρ : V → X) → Homo σeq (rec ρ) (FreeAlg V) B
    recHomo ρ .Homo.op-hom op x y eq = cong (rec ρ) eq

    module _ {V : Type ℓv} (ρ : V → X)
      (f : FreeModel V → X) (ϕ : Homo σeq f (FreeAlg V) B) where

      uniqClo : (e : E.eqns) (ρ' : E.vars e → FreeModel V)
        (ih : ∀ w → f (ρ' w) ≡ rec ρ (ρ' w)) (M : Tm σ (E.vars e))
        → f (clo e M ρ') ≡ rec ρ (clo e M ρ')
      uniqClo e ρ' ih M =
        cong f (cloTmRec e ρ' M)
        ∙ Homo-Tm ϕ ρ' M
        ∙ (λ i → B.⟦ (λ w → ih w i) ⟧Tm M)

      uniqNode : (op : σ .ops) (ts : σ .arities op → FreeModel V)
        (ih : ∀ a → f (ts a) ≡ rec ρ (ts a))
        → f (node op ts) ≡ rec ρ (node op ts)
      uniqNode op ts ih =
        Homo.op-hom' ϕ op ts
        ∙ (λ i → B.⟨ op ⟩⟦ (λ a → ih a i) ⟧op)

      recUniq : (fβ : ∀ v → f (var v) ≡ ρ v)
        (x : FreeModel V) → f x ≡ rec ρ x
      recUniq fβ (var v) = fβ v
      recUniq fβ (node op ts) =
        uniqNode op ts (λ a → recUniq fβ (ts a))
      recUniq fβ (clo e M ρ') =
        uniqClo e ρ' (λ w → recUniq fβ (ρ' w)) M
      recUniq fβ (cloVar e w ρ' i) =
        isProp→PathP
          (λ i → isSetX (f (cloVar e w ρ' i)) (rec ρ (cloVar e w ρ' i)))
          (uniqClo e ρ' (λ w' → recUniq fβ (ρ' w')) (var w))
          (recUniq fβ (ρ' w)) i
      recUniq fβ (cloNode e op ts ρ' i) =
        isProp→PathP
          (λ i → isSetX (f (cloNode e op ts ρ' i))
                        (rec ρ (cloNode e op ts ρ' i)))
          (uniqClo e ρ' (λ w → recUniq fβ (ρ' w)) (node op ts))
          (uniqNode op (λ a → clo e (ts a) ρ')
            (λ a → uniqClo e ρ' (λ w → recUniq fβ (ρ' w)) (ts a))) i
      recUniq fβ (eqn e ρ' i) =
        isProp→PathP
          (λ i → isSetX (f (eqn e ρ' i)) (rec ρ (eqn e ρ' i)))
          (uniqClo e ρ' (λ w → recUniq fβ (ρ' w)) (E.lhs e))
          (uniqClo e ρ' (λ w → recUniq fβ (ρ' w)) (E.rhs e)) i
      recUniq fβ (trunc x y p q i j) =
        isProp→SquareP
          (λ i j → isSetX (f (trunc x y p q i j))
                          (rec ρ (trunc x y p q i j)))
          (λ _ → recUniq fβ x) (λ _ → recUniq fβ y)
          (λ k → recUniq fβ (p k)) (λ k → recUniq fβ (q k)) i j

  -- The universal property: `FreeOb V` is free on `V`, i.e. initial in
  -- the coslice `V ↓ Forget`.
  ℓFree : Level
  ℓFree = ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓv)

  FreeOb : (V : Type ℓv) → Category.ob (MOD σeq ℓFree)
  FreeOb V = (FreeModel V , trunc) , FreeAlg V

  gen : (V : Type ℓv) → V → FreeModel V
  gen V = var

  UPMod : (V : Type ℓv) (N : Category.ob (MOD σeq ℓFree))
    → Iso (ModHom σeq ℓFree (FreeOb V) N) (V → ⟨ N .fst ⟩)
  UPMod V N .Iso.fun (f , _) v = f (gen V v)
  UPMod V N .Iso.inv ρ =
    rec (N .fst .snd) (N .snd) ρ , recHomo (N .fst .snd) (N .snd) ρ
  UPMod V N .Iso.sec ρ = refl
  UPMod V N .Iso.ret (f , ϕ) =
    Σ≡Prop (λ _ → isPropHomo σeq (N .fst .snd))
      (funExt (λ x →
        sym (recUniq (N .fst .snd) (N .snd) _ f ϕ (λ _ → refl) x)))

  isInitialFreeOb : isInitial (MOD σeq ℓFree) (FreeOb (⊥* {ℓv}))
  isInitialFreeOb N =
    isOfHLevelRetractFromIso 0 (UPMod (⊥* {ℓv}) N)
      ((λ ()) , (λ f → funExt (λ ())))

  InitialMOD : Initial (MOD σeq ℓFree)
  InitialMOD = FreeOb (⊥* {ℓv}) , isInitialFreeOb

-- ---------------------------------------------------------------------
-- Comparison: the naive presentation
--
-- `Cubical.Algebra.Theory.Free`'s HIT, reproduced here so the two
-- constructions can be read side by side.  Note that it sits at exactly
-- the same level as `FreeModel` above: the universe bump was never a
-- cost of the naive presentation, it was a cost of `Free.Explicit`'s
-- `{W : Type ℓv}`-quantified substitution constructor.  What the naive
-- presentation costs is the recursor, and the commented attempts below
-- pin down exactly which call it dies on.
-- ---------------------------------------------------------------------
module Naive {σ : AlgTheorySig ℓ ℓ'} (σeq : AlgTheoryEqns σ ℓ'' ℓv) where
  private module E = AlgTheoryEqns σeq

  data NaiveFree (V : Type ℓv)
    : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓv)) where
    var : V → NaiveFree V
    node : (op : σ .ops) → (σ .arities op → NaiveFree V) → NaiveFree V
    eqn : (e : E.eqns) (ρ : E.vars e → NaiveFree V)
      → TmRec node ρ (E.lhs e) ≡ TmRec node ρ (E.rhs e)
    trunc : isSet (NaiveFree V)

  -- The algebra structure is immediate: `node` and `eqn` are literally
  -- the two fields of `Alg`.  Contrast `FreeAlg` above, which needs the
  -- `cloTmRec` bridge.
  NaiveAlg : (V : Type ℓv) → Alg σeq (NaiveFree V)
  NaiveAlg V .Alg.⟨_⟩⟦_⟧op = node
  NaiveAlg V .Alg.⟦_⟧eqn = eqn

  -- Both of the pieces one would want are individually fine.  First,
  -- the prop-valued eliminator's `Tm`-indexed half: structural in `M`.
  module _ {V : Type ℓv} (P : NaiveFree V → Type ℓX)
    (isPropP : ∀ x → isProp (P x))
    (pvar : ∀ v → P (var v))
    (pnode : ∀ op {ts : σ .arities op → NaiveFree V}
      → (∀ a → P (ts a)) → P (node op ts))
    where
    elimPropTm : {W : Type ℓv} (ρ : W → NaiveFree V)
      (ih : ∀ w → P (ρ w)) (M : Tm σ W) → P (TmRec node ρ M)
    elimPropTm ρ ih (var w) = ih w
    elimPropTm ρ ih (node op ts) =
      pnode op (λ a → elimPropTm ρ ih (ts a))

  -- Second, the fusion lemma.  Stated for an arbitrary `h` satisfying
  -- the `node` computation rule one would want of `rec`, it is
  -- structural in `M` all by itself and needs nothing else.  The
  -- problem is never this lemma in isolation.
  module _ {X : Type ℓX} (B : Alg σeq X) where
    private module B = Alg B

    fuseGen : {V : Type ℓv} (h : NaiveFree V → X)
      (hnode : ∀ op (ts : σ .arities op → NaiveFree V)
        → h (node op ts) ≡ B.⟨ op ⟩⟦ (λ a → h (ts a)) ⟧op)
      {W : Type ℓv} (ρ' : W → NaiveFree V) (M : Tm σ W)
      → h (TmRec node ρ' M) ≡ B.⟦ (λ w → h (ρ' w)) ⟧Tm M
    fuseGen h hnode ρ' (var w) = refl
    fuseGen h hnode ρ' (node op ts) =
      hnode op (λ a → TmRec node ρ' (ts a))
      ∙ (λ i → B.⟨ op ⟩⟦ (λ a → fuseGen h hnode ρ' (ts a) i) ⟧op)

-- ---------------------------------------------------------------------
-- Where the naive presentation breaks.
--
-- Everything below was run against this file and rejected; the errors
-- are verbatim.  The root cause is uniform: `eqn`'s endpoints are
-- `TmRec node ρ (lhs e)`, a STUCK application of an external fold, not
-- a constructor application.  So the boundary that Agda demands of the
-- `eqn` clause of any function defined on `NaiveFree` is a call of that
-- function at a term the fold builds, which is not a structural subterm
-- of `eqn e ρ i`.  `clo` above exists precisely to make that endpoint a
-- constructor application instead.
--
-- (1) The prop-valued eliminator, endpoints supplied by `elimPropTm`.
--
--   elimProp : (x : NaiveFree V) → P x
--   elimProp (var v) = pvar v
--   elimProp (node op ts) = pnode op (λ a → elimProp (ts a))
--   elimProp (eqn e ρ i) =
--     isProp→PathP (λ i → isPropP (eqn e ρ i))
--       (elimPropTm ρ (λ w → elimProp (ρ w)) (E.lhs e))
--       (elimPropTm ρ (λ w → elimProp (ρ w)) (E.rhs e)) i
--   elimProp (trunc x y p q i j) = ...
--
-- error: [UnequalTerms]
-- The terms
--   elimProp (TmRec node ρ (AlgTheoryEqns.lhs σeq₁ e))
-- and
--   elimPropTm ρ (λ w → elimProp (ρ w)) (AlgTheoryEqns.lhs σeq₁ e)
-- are not equal at type P₁ (eqn e ρ i0)
-- when checking the definition of elimProp
--
-- i.e. `isProp` does NOT discharge the `eqn` case: the boundary is a
-- definitional demand, and `elimPropTm ρ _ (lhs e)` is a different
-- stuck term from `elimProp (TmRec node ρ (lhs e))`.  Writing the
-- boundary as `_ _` instead only turns this into two unsolved metas
-- blocked on the same two terms.
--
-- (2) The prop-valued eliminator, endpoints written as Agda demands.
--
--   elimProp (eqn e ρ i) =
--     isProp→PathP (λ i → isPropP (eqn e ρ i))
--       (elimProp (TmRec node ρ (E.lhs e)))
--       (elimProp (TmRec node ρ (E.rhs e))) i
--
-- error: [TerminationIssue]
-- Termination checking failed for the following function:
--   elimProp
-- Problematic call:
--   elimProp (TmRec node ρ (AlgTheoryEqns.rhs σeq e))
--
-- So the sharp boundary is one notch lower than `Free.agda`'s closing
-- comment suggests: not even the prop-valued eliminator survives by
-- direct pattern matching.  The recursion IS well founded -- descend on
-- `M` down to the `ρ w`, which is what `elimPropTm` does -- but Agda
-- cannot use that measure, because the clause boundary forces the
-- syntactic form `elimProp (TmRec node ρ (lhs e))`.
--
-- (3) `rec` and `fuse` defined mutually.
--
--   rec : {V : Type ℓv} (ρ : V → X) → NaiveFree V → X
--   fuse : {V W : Type ℓv} (ρ : V → X) (ρ' : W → NaiveFree V)
--     (M : Tm σ W) → rec ρ (TmRec node ρ' M)
--     ≡ B.⟦ (λ w → rec ρ (ρ' w)) ⟧Tm M
--   rec ρ (var v) = ρ v
--   rec ρ (node op ts) = B.⟨ op ⟩⟦ (λ a → rec ρ (ts a)) ⟧op
--   rec ρ (eqn e ρ' i) =
--     (fuse ρ ρ' (E.lhs e)
--      ∙ B.⟦ e ⟧eqn (λ w → rec ρ (ρ' w))
--      ∙ sym (fuse ρ ρ' (E.rhs e))) i
--   rec ρ (trunc x y p q i j) = ...
--   fuse ρ ρ' (var w) = refl
--   fuse ρ ρ' (node op ts) =
--     λ i → B.⟨ op ⟩⟦ (λ a → fuse ρ ρ' (ts a) i) ⟧op
--
-- error: [TerminationIssue]
-- Termination checking failed for the following function:
--   rec
-- Problematic call:
--   rec ρ (TmRec node ρ' (AlgTheoryEqns.rhs σeq e))
--
-- The offending call is reported at the occurrence of `rec` in `fuse`'s
-- TYPE.  `rec`'s `eqn` clause calls `fuse ρ ρ' (rhs e)`, and that call
-- carries `rec ρ (TmRec node ρ' (rhs e))` in its type -- a `rec → rec`
-- call at a term built by the fold, not a subterm of `eqn e ρ' i`.
--
-- (4) `rec` alone, with the fusion generalised over `h` (`fuseGen`
--     above, which type-checks) instantiated at `h := rec ρ`.
--
--   rec ρ (eqn e ρ' i) =
--     (fuseGen B (rec ρ) (λ op ts → refl) ρ' (E.lhs e)
--      ∙ B.⟦ e ⟧eqn (λ w → rec ρ (ρ' w))
--      ∙ sym (fuseGen B (rec ρ) (λ op ts → refl) ρ' (E.rhs e))) i
--
-- error: [TerminationIssue]
-- Termination checking failed for the following function:
--   rec
-- Problematic call:
--   rec ρ
--
-- Generalising only relocates the problem, as `Free.agda` says: the
-- partial application `rec ρ` handed to `fuseGen` is a `rec → rec` call
-- of unknown size, so there is nothing to descend on.
-- ---------------------------------------------------------------------
