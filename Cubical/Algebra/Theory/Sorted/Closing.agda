-- The free model of a MANY-SORTED theory, presented with a closing
-- substitution for the equation endpoints only.
--
-- This is the sorted port of `Cubical.Algebra.Theory.Free.Closing`.
-- Contrast `Cubical.Algebra.Theory.Sorted`'s `FreeModel`, whose
-- substitution constructor quantifies over an arbitrary `W : Type ℓv`
-- and therefore lands in a universe `ℓ-suc ℓv`.  Here the only
-- substitutions in the syntax are the ones the equations need, so the
-- variable context is `σeq .vars e` -- determined by `e : eqns` -- and
-- there is no universe bump.
module Cubical.Algebra.Theory.Sorted.Closing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Initial

open import Cubical.Algebra.Theory.Sorted
  using (SortedSig; SortedEqns; Tm; var; node; Ops; TmRec;
         FAM; ALGᴰ; ALG; EQNSᴰ; MODᴰ; MOD; ModHom)

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX : Level

open SortedSig
open SortedEqns

-- The level of the free model.  Note the absence of `ℓ-suc ℓv`, which
-- `Cubical.Algebra.Theory.Sorted.ℓFree` pays for its `{W : Type ℓv}`.
ℓClosing : (ℓS ℓ ℓ' ℓ'' ℓv : Level) → Level
ℓClosing ℓS ℓ ℓ' ℓ'' ℓv =
  ℓ-max (ℓ-max ℓS ℓ) (ℓ-max (ℓ-max ℓ' ℓ'') ℓv)

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' ℓv) where

  data FreeModel (V : Type ℓv) (vs : V → S)
    : S → Type (ℓClosing ℓS ℓ ℓ' ℓ'' ℓv) where
    var : (v : V) → FreeModel V vs (vs v)
    node : (o : σ .ops)
      → ((a : σ .arities o) → FreeModel V vs (σ .sortOf o a))
      → FreeModel V vs (σ .resultSort o)
    clo : (e : σeq .eqns) {s : S}
      → Tm σ (σeq .vars e) (σeq .varSort e) s
      → ((w : σeq .vars e) → FreeModel V vs (σeq .varSort e w))
      → FreeModel V vs s
    cloVar : (e : σeq .eqns) (w : σeq .vars e)
      (ρ : (w' : σeq .vars e) → FreeModel V vs (σeq .varSort e w'))
      → clo e (var w) ρ ≡ ρ w
    cloNode : (e : σeq .eqns) (o : σ .ops)
      (ts : (a : σ .arities o)
          → Tm σ (σeq .vars e) (σeq .varSort e) (σ .sortOf o a))
      (ρ : (w : σeq .vars e) → FreeModel V vs (σeq .varSort e w))
      → clo e (node o ts) ρ ≡ node o (λ a → clo e (ts a) ρ)
    eqn : (e : σeq .eqns)
      (ρ : (w : σeq .vars e) → FreeModel V vs (σeq .varSort e w))
      → clo e (σeq .lhs e) ρ ≡ clo e (σeq .rhs e) ρ
    trunc : {s : S} → isSet (FreeModel V vs s)

  module _ {V : Type ℓv} {vs : V → S} where

    -- `⊥`/`Bool` arities have no definitional η, so the selector a
    -- named term builder produces is never syntactically the one
    -- `TmRec` produces.  This is the bridge; it also disambiguates the
    -- overloaded constructor `node`.
    opCong : (o : σ .ops)
      {g h : (a : σ .arities o) → FreeModel V vs (σ .sortOf o a)}
      → ((a : σ .arities o) → g a ≡ h a)
      → Path (FreeModel V vs (σ .resultSort o)) (node o g) (node o h)
    opCong o p i = node o (λ a → p a i)

    -- `clo` is determined by induction on the term: `cloVar`/`cloNode`
    -- say it agrees with the external recursor `TmRec _ node`.
    cloTmRec : (e : σeq .eqns)
      (ρ : (w : σeq .vars e) → FreeModel V vs (σeq .varSort e w))
      {s : S} (M : Tm σ (σeq .vars e) (σeq .varSort e) s)
      → clo e M ρ ≡ TmRec (FreeModel V vs) node ρ M
    cloTmRec e ρ (var w) = cloVar e w ρ
    cloTmRec e ρ (node o ts) =
      cloNode e o ts ρ
      ∙ opCong o (λ a → cloTmRec e ρ (ts a))

    FreeOps : Ops {σ = σ} (FreeModel V vs)
    FreeOps = node

    FreeEqns : (e : σeq .eqns)
      (ρ : (w : σeq .vars e) → FreeModel V vs (σeq .varSort e w))
      → TmRec (FreeModel V vs) node ρ (σeq .lhs e)
        ≡ TmRec (FreeModel V vs) node ρ (σeq .rhs e)
    FreeEqns e ρ =
      sym (cloTmRec e ρ (σeq .lhs e))
      ∙ eqn e ρ
      ∙ cloTmRec e ρ (σeq .rhs e)

  module _ {X : S → Type ℓX} (isSetX : (s : S) → isSet (X s))
    (α : Ops {σ = σ} X)
    (sat : (e : σeq .eqns)
           (ρ : (w : σeq .vars e) → X (σeq .varSort e w))
         → TmRec X α ρ (σeq .lhs e) ≡ TmRec X α ρ (σeq .rhs e)) where

    -- No `TERMINATING` pragma: `clo`'s argument is a `Tm`, so the
    -- boundary of the two path clauses is a term this very definition
    -- already computes on structural subterms.
    rec : {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v))
      {s : S} → FreeModel V vs s → X s
    rec ρ (var v) = ρ v
    rec ρ (node o ts) = α o (λ a → rec ρ (ts a))
    rec ρ (clo e M ρ') = TmRec X α (λ w → rec ρ (ρ' w)) M
    rec ρ (cloVar e w ρ' i) = rec ρ (ρ' w)
    rec ρ (cloNode e o ts ρ' i) =
      α o (λ a → TmRec X α (λ w → rec ρ (ρ' w)) (ts a))
    rec ρ (eqn e ρ' i) = sat e (λ w → rec ρ (ρ' w)) i
    rec ρ (trunc x y p q i j) =
      isSetX _ (rec ρ x) (rec ρ y) (cong (rec ρ) p) (cong (rec ρ) q) i j

    recβ : {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v)) (v : V)
      → rec ρ (var v) ≡ ρ v
    recβ ρ v = refl

    -- the forded homomorphism condition of `ALGᴰ`
    recHomo : {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v))
      (o : σ .ops)
      (x : (a : σ .arities o) → FreeModel V vs (σ .sortOf o a))
      (y : FreeModel V vs (σ .resultSort o)) → y ≡ node o x
      → rec ρ y ≡ α o (λ a → rec ρ (x a))
    recHomo ρ o x y eq = cong (rec ρ {s = σ .resultSort o}) eq

    module _ {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v))
      (f : (s : S) → FreeModel V vs s → X s)
      (ϕ : (o : σ .ops)
           (x : (a : σ .arities o) → FreeModel V vs (σ .sortOf o a))
           (y : FreeModel V vs (σ .resultSort o)) → y ≡ node o x
         → f (σ .resultSort o) y ≡ α o (λ a → f (σ .sortOf o a) (x a)))
      where

      Homo-Tm : {W : Type ℓv} {ws : W → S}
        (ρ' : (w : W) → FreeModel V vs (ws w))
        {s : S} (M : Tm σ W ws s)
        → f s (TmRec (FreeModel V vs) node ρ' M)
          ≡ TmRec X α (λ w → f (ws w) (ρ' w)) M
      Homo-Tm ρ' (var w) = refl
      Homo-Tm ρ' (node o ts) =
        ϕ o (λ a → TmRec (FreeModel V vs) node ρ' (ts a))
          (node o (λ a → TmRec (FreeModel V vs) node ρ' (ts a))) refl
        ∙ (λ i → α o (λ a → Homo-Tm ρ' (ts a) i))

      uniqNode : (o : σ .ops)
        (ts : (a : σ .arities o) → FreeModel V vs (σ .sortOf o a))
        (ih : (a : σ .arities o)
            → f (σ .sortOf o a) (ts a) ≡ rec ρ (ts a))
        → f (σ .resultSort o) (node o ts) ≡ rec ρ (node o ts)
      uniqNode o ts ih =
        ϕ o ts (node o ts) refl ∙ (λ i → α o (λ a → ih a i))

      uniqClo : (e : σeq .eqns)
        (ρ' : (w : σeq .vars e) → FreeModel V vs (σeq .varSort e w))
        (ih : (w : σeq .vars e)
            → f (σeq .varSort e w) (ρ' w) ≡ rec ρ (ρ' w))
        {s : S} (M : Tm σ (σeq .vars e) (σeq .varSort e) s)
        → f s (clo e M ρ') ≡ rec ρ (clo e M ρ')
      uniqClo e ρ' ih {s} M =
        cong (f s) (cloTmRec e ρ' M)
        ∙ Homo-Tm ρ' M
        ∙ (λ i → TmRec X α (λ w → ih w i) M)

      module _ (fβ : (v : V) → f (vs v) (var v) ≡ ρ v) where

        recUniq : {s : S} (x : FreeModel V vs s) → f s x ≡ rec ρ x
        recUniq (var v) = fβ v
        recUniq (node o ts) = uniqNode o ts (λ a → recUniq (ts a))
        recUniq (clo e M ρ') = uniqClo e ρ' (λ w → recUniq (ρ' w)) M
        recUniq (cloVar e w ρ' i) =
          isProp→PathP
            (λ i → isSetX _ (f _ (cloVar e w ρ' i))
                            (rec ρ (cloVar e w ρ' i)))
            (uniqClo e ρ' (λ w' → recUniq (ρ' w')) (var w))
            (recUniq (ρ' w)) i
        recUniq (cloNode e o ts ρ' i) =
          isProp→PathP
            (λ i → isSetX _ (f _ (cloNode e o ts ρ' i))
                            (rec ρ (cloNode e o ts ρ' i)))
            (uniqClo e ρ' (λ w → recUniq (ρ' w)) (node o ts))
            (uniqNode o (λ a → clo e (ts a) ρ')
              (λ a → uniqClo e ρ' (λ w → recUniq (ρ' w)) (ts a))) i
        recUniq (eqn e ρ' i) =
          isProp→PathP
            (λ i → isSetX _ (f _ (eqn e ρ' i)) (rec ρ (eqn e ρ' i)))
            (uniqClo e ρ' (λ w → recUniq (ρ' w)) (σeq .lhs e))
            (uniqClo e ρ' (λ w → recUniq (ρ' w)) (σeq .rhs e)) i
        recUniq (trunc x y p q i j) =
          isProp→SquareP
            (λ i j → isSetX _ (f _ (trunc x y p q i j))
                              (rec ρ (trunc x y p q i j)))
            (λ _ → recUniq x) (λ _ → recUniq y)
            (λ k → recUniq (p k)) (λ k → recUniq (q k)) i j

  -- The universal property: `FreeOb V vs` is free on the sorted set
  -- (V , vs), i.e. initial in (V , vs) ↓ Forget.
  private
    ℓC = ℓClosing ℓS ℓ ℓ' ℓ'' ℓv

  FreeOb : (V : Type ℓv) (vs : V → S) → Category.ob (MOD σeq ℓC)
  FreeOb V vs = (λ s → FreeModel V vs s , trunc) , FreeOps , FreeEqns

  gen : (V : Type ℓv) (vs : V → S) (v : V) → FreeModel V vs (vs v)
  gen V vs = var

  module _ (V : Type ℓv) (vs : V → S) (N : Category.ob (MOD σeq ℓC))
    where
    private
      Y : S → Type ℓC
      Y s = ⟨ N .fst s ⟩

      isSetY : (s : S) → isSet (Y s)
      isSetY s = N .fst s .snd

      β = N .snd .fst
      sat = N .snd .snd

    UPMod : Iso (ModHom σeq ℓC (FreeOb V vs) N) ((v : V) → Y (vs v))
    UPMod .Iso.fun (f , _) v = f (vs v) (gen V vs v)
    UPMod .Iso.inv ρ =
      (λ _ → rec isSetY β sat ρ)
      , recHomo isSetY β sat ρ
      , tt*
    UPMod .Iso.sec ρ = refl
    UPMod .Iso.ret (f , ϕ , _) =
      Σ≡Prop
        (λ _ → isPropΣ (isPropΠ4 (λ _ _ _ _ → isSetY _ _ _))
                       (λ _ → isPropUnit*))
        (funExt (λ s → funExt (λ x →
          sym (recUniq isSetY β sat _ f ϕ (λ _ → refl) x))))

  isInitialFreeOb : isInitial (MOD σeq ℓC) (FreeOb (⊥* {ℓv}) (λ ()))
  isInitialFreeOb N =
    isOfHLevelRetractFromIso 0 (UPMod (⊥* {ℓv}) (λ ()) N)
      ((λ ()) , (λ f → funExt (λ ())))

  InitialMOD : Initial (MOD σeq ℓC)
  InitialMOD = FreeOb (⊥* {ℓv}) (λ ()) , isInitialFreeOb
