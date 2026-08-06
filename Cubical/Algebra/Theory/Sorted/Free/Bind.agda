-- The bind-based free model of a many-sorted theory.
--
-- Substitution is a *constructor*: `⟦ M ⟧ ρ` binds a term `M` over an
-- arbitrary variable context to an environment `ρ`.  That is what buys
-- the recursor `rec` and its uniqueness `recUniq`, and hence the
-- universal property `UPMod` and initiality `InitialMOD` — the naive
-- presentation has none of these.  It is also what costs a universe:
-- quantifying over `{W : Type ℓv}` forces the carrier to `ℓ-suc ℓv`.
--
-- `Cubical.Algebra.Theory.Sorted.Free.Closing` gives the other working
-- presentation, which pays no such cost.  See
-- `Cubical.Algebra.Theory.Sorted.Free.Comparison` for the two side by
-- side, and for the naive presentation that fails.
module Cubical.Algebra.Theory.Sorted.Free.Bind where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Initial

open import Cubical.Algebra.Theory.Sorted

open SortedSig
open SortedEqns

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX : Level

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' ℓv) where

  data FreeModel (V : Type ℓv) (vs : V → S)
    : S → Type (ℓ-max (ℓ-max ℓS ℓ)
                (ℓ-max (ℓ-max ℓ' ℓ'') (ℓ-suc ℓv))) where
    gen : (v : V) → FreeModel V vs (vs v)
    opF : (o : σ .ops)
      → ((a : σ .arities o) → FreeModel V vs (σ .sortOf o a))
      → FreeModel V vs (σ .resultSort o)
    ⟦_⟧_ : {s : S} {W : Type ℓv} {ws : W → S} → Tm σ W ws s
      → ((w : W) → FreeModel V vs (ws w)) → FreeModel V vs s
    ⟦var⟧ : {W : Type ℓv} {ws : W → S} (w : W)
      (ρ : (w' : W) → FreeModel V vs (ws w')) → ⟦ var w ⟧ ρ ≡ ρ w
    ⟦node⟧ : {W : Type ℓv} {ws : W → S} (o : σ .ops)
      (ts : (a : σ .arities o) → Tm σ W ws (σ .sortOf o a))
      (ρ : (w : W) → FreeModel V vs (ws w))
      → ⟦ node o ts ⟧ ρ ≡ opF o (λ a → ⟦ ts a ⟧ ρ)
    eqn : (e : σeq .eqns)
      (ρ : (v : σeq .vars e) → FreeModel V vs (σeq .varSort e v))
      → ⟦ σeq .lhs e ⟧ ρ ≡ ⟦ σeq .rhs e ⟧ ρ
    trunc : {s : S} → isSet (FreeModel V vs s)

  module _ {V : Type ℓv} {vs : V → S} where

    TmRec-⟦⟧ : {W : Type ℓv} {ws : W → S}
      (ρ : (w : W) → FreeModel V vs (ws w))
      {s : S} (M : Tm σ W ws s) → TmRec (FreeModel V vs) opF ρ M ≡ ⟦ M ⟧ ρ
    TmRec-⟦⟧ ρ (var w) = sym (⟦var⟧ w ρ)
    TmRec-⟦⟧ ρ (node o ts) =
      cong (opF o) (funExt (λ a → TmRec-⟦⟧ ρ (ts a)))
      ∙ sym (⟦node⟧ o ts ρ)

    FreeOps : Ops (FreeModel V vs)
    FreeOps = opF

    opCong : (o : σ .ops)
      {g h : (a : σ .arities o) → FreeModel V vs (σ .sortOf o a)}
      → ((a : σ .arities o) → g a ≡ h a) → opF o g ≡ opF o h
    opCong o p = cong (opF o) (funExt p)

    FreeEqns : (e : σeq .eqns)
      (ρ : (v : σeq .vars e) → FreeModel V vs (σeq .varSort e v))
      → TmRec (FreeModel V vs) opF ρ (σeq .lhs e)
        ≡ TmRec (FreeModel V vs) opF ρ (σeq .rhs e)
    FreeEqns e ρ =
      TmRec-⟦⟧ ρ (σeq .lhs e) ∙ eqn e ρ ∙ sym (TmRec-⟦⟧ ρ (σeq .rhs e))

  module _ {X : S → Type ℓX} (isSetX : (s : S) → isSet (X s))
    (α : Ops X)
    (sat : (e : σeq .eqns)
           (ρ : (v : σeq .vars e) → X (σeq .varSort e v))
         → TmRec X α ρ (σeq .lhs e) ≡ TmRec X α ρ (σeq .rhs e)) where

    rec : {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v))
      {s : S} → FreeModel V vs s → X s
    rec ρ (gen v) = ρ v
    rec ρ (opF o ts) = α o (λ a → rec ρ (ts a))
    rec ρ (⟦ M ⟧ ρ') = TmRec X α (λ w → rec ρ (ρ' w)) M
    rec ρ (⟦var⟧ w ρ' i) = rec ρ (ρ' w)
    rec ρ (⟦node⟧ o ts ρ' i) =
      α o (λ a → TmRec X α (λ w → rec ρ (ρ' w)) (ts a))
    rec ρ (eqn e ρ' i) = sat e (λ w → rec ρ (ρ' w)) i
    rec ρ (trunc x y p q i j) =
      isSetX _ (rec ρ x) (rec ρ y) (cong (rec ρ) p) (cong (rec ρ) q) i j

    module _ {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v))
      (f : (s : S) → FreeModel V vs s → X s)
      (ϕ : (o : σ .ops)
           (x : (a : σ .arities o) → FreeModel V vs (σ .sortOf o a))
           (y : FreeModel V vs (σ .resultSort o)) → y ≡ opF o x
         → f (σ .resultSort o) y ≡ α o (λ a → f (σ .sortOf o a) (x a)))
      (fβ : (v : V) → f (vs v) (gen v) ≡ ρ v) where

      HomoTm : {W : Type ℓv} {ws : W → S}
        (ρ' : (w : W) → FreeModel V vs (ws w))
        {s : S} (M : Tm σ W ws s)
        → f s (TmRec (FreeModel V vs) opF ρ' M)
          ≡ TmRec X α (λ w → f (ws w) (ρ' w)) M
      HomoTm ρ' (var w) = refl
      HomoTm ρ' (node o ts) =
        ϕ o _ _ refl ∙ cong (α o) (funExt (λ a → HomoTm ρ' (ts a)))

      uniqOp : (o : σ .ops)
        (ts : (a : σ .arities o) → FreeModel V vs (σ .sortOf o a))
        (ih : (a : σ .arities o)
            → f (σ .sortOf o a) (ts a) ≡ rec ρ (ts a))
        → f (σ .resultSort o) (opF o ts) ≡ rec ρ (opF o ts)
      uniqOp o ts ih = ϕ o ts (opF o ts) refl ∙ cong (α o) (funExt ih)

      uniqSub : {W : Type ℓv} {ws : W → S}
        (ρ' : (w : W) → FreeModel V vs (ws w))
        (ih : (w : W) → f (ws w) (ρ' w) ≡ rec ρ (ρ' w))
        {s : S} (M : Tm σ W ws s) → f s (⟦ M ⟧ ρ') ≡ rec ρ (⟦ M ⟧ ρ')
      uniqSub ρ' ih M =
        cong (f _) (sym (TmRec-⟦⟧ ρ' M))
        ∙ HomoTm ρ' M
        ∙ cong (λ k → TmRec X α k M) (funExt ih)

      recUniq : {s : S} (x : FreeModel V vs s) → f s x ≡ rec ρ x
      recUniq (gen v) = fβ v
      recUniq (opF o ts) = uniqOp o ts (λ a → recUniq (ts a))
      recUniq (⟦ M ⟧ ρ') = uniqSub ρ' (λ w → recUniq (ρ' w)) M
      recUniq (⟦var⟧ w ρ' i) =
        isProp→PathP
          (λ i → isSetX _ (f _ (⟦var⟧ w ρ' i)) (rec ρ (⟦var⟧ w ρ' i)))
          (uniqSub ρ' (λ w' → recUniq (ρ' w')) (var w))
          (recUniq (ρ' w)) i
      recUniq (⟦node⟧ o ts ρ' i) =
        isProp→PathP
          (λ i → isSetX _ (f _ (⟦node⟧ o ts ρ' i))
                          (rec ρ (⟦node⟧ o ts ρ' i)))
          (uniqSub ρ' (λ w → recUniq (ρ' w)) (node o ts))
          (uniqOp o (λ a → ⟦ ts a ⟧ ρ')
            (λ a → uniqSub ρ' (λ w → recUniq (ρ' w)) (ts a))) i
      recUniq (eqn e ρ' i) =
        isProp→PathP
          (λ i → isSetX _ (f _ (eqn e ρ' i)) (rec ρ (eqn e ρ' i)))
          (uniqSub ρ' (λ w → recUniq (ρ' w)) (σeq .lhs e))
          (uniqSub ρ' (λ w → recUniq (ρ' w)) (σeq .rhs e)) i
      recUniq (trunc x y p q i j) =
        isProp→SquareP
          (λ i j → isSetX _ (f _ (trunc x y p q i j))
                            (rec ρ (trunc x y p q i j)))
          (λ _ → recUniq x) (λ _ → recUniq y)
          (λ k → recUniq (p k)) (λ k → recUniq (q k)) i j

-- The universal property: `FreeOb V vs` is free on the sorted set
-- (V , vs), i.e. initial in (V , vs) ↓ Forget.  Nothing here mentions
-- the signature beyond `MOD`, so every instance gets it for free.
ℓFree : (ℓS ℓ ℓ' ℓ'' ℓv : Level) → Level
ℓFree ℓS ℓ ℓ' ℓ'' ℓv =
  ℓ-max (ℓ-max ℓS ℓ) (ℓ-max (ℓ-max ℓ' ℓ'') (ℓ-suc ℓv))

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' ℓv) where

  private
    ℓF = ℓFree ℓS ℓ ℓ' ℓ'' ℓv

  FreeOb : (V : Type ℓv) (vs : V → S) → Category.ob (MOD σeq ℓF)
  FreeOb V vs = (λ s → FreeModel σeq V vs s , trunc) , opF , FreeEqns σeq

  module _ (V : Type ℓv) (vs : V → S) (N : Category.ob (MOD σeq ℓF)) where
    private
      Y : S → Type ℓF
      Y s = ⟨ N .fst s ⟩

      isSetY : (s : S) → isSet (Y s)
      isSetY s = N .fst s .snd

      β = N .snd .fst
      sat = N .snd .snd

    UPMod : Iso (ModHom σeq ℓF (FreeOb V vs) N)
                ((v : V) → Y (vs v))
    UPMod .Iso.fun (f , _) v = f (vs v) (gen v)
    UPMod .Iso.inv ρ =
      (λ _ → rec σeq isSetY β sat ρ)
      , (λ o x y eq → cong (rec σeq isSetY β sat ρ) eq)
      , tt*
    UPMod .Iso.sec ρ = refl
    UPMod .Iso.ret (f , ϕ , _) =
      Σ≡Prop
        (λ _ → isPropΣ (isPropΠ4 (λ _ _ _ _ → isSetY _ _ _))
                       (λ _ → isPropUnit*))
        (funExt (λ s → funExt (λ x →
          sym (recUniq σeq isSetY β sat _ f ϕ (λ _ → refl) x))))

  isInitialFreeOb : isInitial (MOD σeq ℓF) (FreeOb (⊥* {ℓv}) (λ ()))
  isInitialFreeOb N =
    isOfHLevelRetractFromIso 0 (UPMod (⊥* {ℓv}) (λ ()) N)
      ((λ ()) , (λ f → funExt (λ ())))

  InitialMOD : Initial (MOD σeq ℓF)
  InitialMOD = FreeOb (⊥* {ℓv}) (λ ()) , isInitialFreeOb
