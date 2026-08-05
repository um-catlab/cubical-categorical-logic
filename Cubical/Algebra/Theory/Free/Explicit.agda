-- The free model presented with explicit substitution.
--
-- `Free.agda`'s presentation makes the equation constructor mention
-- `TmRec node`, an external recursive function, and its recursor is then
-- not definable: the fusion lemma calls `rec` at a non-subterm.  Carrying
-- the term in the constructor instead makes that recursion structural --
-- every recursive call is `rec (ρ w)` with `ρ` constructor data, the
-- W-type pattern -- and the fusion becomes definitional, so the equation
-- clause is just the model's own equation.
--
-- Costs: the arity and variable levels must agree, and the monad laws for
-- `⟦_⟧_` become path constructors.
module Cubical.Algebra.Theory.Free.Explicit where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Algebra.Theory
open AlgTheorySig

module _ {ℓ ℓv} {σ : AlgTheorySig ℓ ℓv} where
  bind : {V W : Type ℓv} → (W → Tm σ V) → Tm σ W → Tm σ V
  bind N (var w) = N w
  bind N (node op ts) = node op (λ a → bind N (ts a))

  TmRec-bind : {ℓX : Level} {X : Type ℓX}
    (α : ∀ (op : σ .ops) → (σ .arities op → X) → X)
    {V W : Type ℓv} (k : V → X) (N : W → Tm σ V) (M : Tm σ W)
    → TmRec α k (bind N M) ≡ TmRec α (λ w → TmRec α k (N w)) M
  TmRec-bind α k N (var w) = refl
  TmRec-bind α k N (node op ts) =
    cong (α op) (funExt (λ a → TmRec-bind α k N (ts a)))

module _ {ℓ ℓ'' ℓv} {σ : AlgTheorySig ℓ ℓv}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) where
  private module E = AlgTheoryEqns σeq

  data FreeModel (V : Type ℓv)
    : Type (ℓ-max (ℓ-max ℓ ℓv) (ℓ-max ℓ'' (ℓ-suc ℓv))) where
    var : V → FreeModel V
    ⟦_⟧_ : {W : Type ℓv} → Tm σ W → (W → FreeModel V) → FreeModel V
    ⟦var⟧ : {W : Type ℓv} (w : W) (ρ : W → FreeModel V) → ⟦ var w ⟧ ρ ≡ ρ w
    ⟦bind⟧ : {W U : Type ℓv} (M : Tm σ W) (N : W → Tm σ U)
      (ρ : U → FreeModel V) → ⟦ M ⟧ (λ w → ⟦ N w ⟧ ρ) ≡ ⟦ bind N M ⟧ ρ
    eqn : (e : E.eqns) (ρ : E.vars e → FreeModel V)
      → ⟦ E.lhs e ⟧ ρ ≡ ⟦ E.rhs e ⟧ ρ
    trunc : isSet (FreeModel V)

  node' : {V : Type ℓv} (op : σ .ops)
    → (σ .arities op → FreeModel V) → FreeModel V
  node' op ts = ⟦ node op var ⟧ ts

  TmRec-⟦⟧ : {V W : Type ℓv} (ρ : W → FreeModel V) (M : Tm σ W)
    → TmRec node' ρ M ≡ ⟦ M ⟧ ρ
  TmRec-⟦⟧ ρ (var w) = sym (⟦var⟧ w ρ)
  TmRec-⟦⟧ ρ (node op ts) =
    cong (λ h → ⟦ node op var ⟧ h) (funExt (λ a → TmRec-⟦⟧ ρ (ts a)))
    ∙ ⟦bind⟧ (node op var) ts ρ

  FreeAlg : (V : Type ℓv) → Alg σeq (FreeModel V)
  FreeAlg V .Alg.⟨_⟩⟦_⟧op = node'
  FreeAlg V .Alg.⟦_⟧eqn e ρ =
    TmRec-⟦⟧ ρ (E.lhs e) ∙ eqn e ρ ∙ sym (TmRec-⟦⟧ ρ (E.rhs e))

  Homo-Tm : {ℓX ℓY : Level} {X : Type ℓX} {Y : Type ℓY} {f : X → Y}
    {B : Alg σeq X} {C : Alg σeq Y} (ϕ : Homo σeq f B C)
    {W : Type ℓv} (ρ : W → X) (M : Tm σ W)
    → f (Alg.⟦_⟧Tm B ρ M) ≡ Alg.⟦_⟧Tm C (λ w → f (ρ w)) M
  Homo-Tm ϕ ρ (var w) = refl
  Homo-Tm {C = C} ϕ ρ (node op ts) =
    Homo.op-hom' ϕ op _
    ∙ cong (Alg.⟨_⟩⟦_⟧op C op) (funExt (λ a → Homo-Tm ϕ ρ (ts a)))

  module _ {ℓX : Level} {X : Type ℓX} (isSetX : isSet X) (B : Alg σeq X) where
    private module B = Alg B

    rec : {V : Type ℓv} (ρ : V → X) → FreeModel V → X
    rec ρ (var v) = ρ v
    rec ρ (⟦ M ⟧ ρ') = B.⟦ (λ w → rec ρ (ρ' w)) ⟧Tm M
    rec ρ (⟦var⟧ w ρ' i) = rec ρ (ρ' w)
    rec ρ (⟦bind⟧ M N ρ' i) =
      sym (TmRec-bind B.⟨_⟩⟦_⟧op (λ u → rec ρ (ρ' u)) N M) i
    rec ρ (eqn e ρ' i) = B.⟦ e ⟧eqn (λ w → rec ρ (ρ' w)) i
    rec ρ (trunc x y p q i j) =
      isSetX (rec ρ x) (rec ρ y) (cong (rec ρ) p) (cong (rec ρ) q) i j

    recHomo : {V : Type ℓv} (ρ : V → X) → Homo σeq (rec ρ) (FreeAlg V) B
    recHomo ρ .Homo.op-hom op x y eq = cong (rec ρ) eq

    recβ : {V : Type ℓv} (ρ : V → X) (v : V) → rec ρ (var v) ≡ ρ v
    recβ ρ v = refl

    uniqSub : {V W : Type ℓv} (ρ : V → X)
      (f : FreeModel V → X) (ϕ : Homo σeq f (FreeAlg V) B)
      (ρ' : W → FreeModel V) (ih : ∀ w → f (ρ' w) ≡ rec ρ (ρ' w))
      (M : Tm σ W) → f (⟦ M ⟧ ρ') ≡ rec ρ (⟦ M ⟧ ρ')
    uniqSub ρ f ϕ ρ' ih M =
      cong f (sym (TmRec-⟦⟧ ρ' M))
      ∙ Homo-Tm ϕ ρ' M
      ∙ cong (λ k → B.⟦ k ⟧Tm M) (funExt ih)

    recUniq : {V : Type ℓv} (ρ : V → X)
      (f : FreeModel V → X) (ϕ : Homo σeq f (FreeAlg V) B)
      (fβ : ∀ v → f (var v) ≡ ρ v)
      → (x : FreeModel V) → f x ≡ rec ρ x
    recUniq ρ f ϕ fβ (var v) = fβ v
    recUniq ρ f ϕ fβ (⟦ M ⟧ ρ') =
      uniqSub ρ f ϕ ρ' (λ w → recUniq ρ f ϕ fβ (ρ' w)) M
    recUniq ρ f ϕ fβ (⟦var⟧ w ρ' i) =
      isProp→PathP (λ i → isSetX (f (⟦var⟧ w ρ' i)) (rec ρ (⟦var⟧ w ρ' i)))
        (uniqSub ρ f ϕ ρ' (λ w' → recUniq ρ f ϕ fβ (ρ' w')) (var w))
        (recUniq ρ f ϕ fβ (ρ' w)) i
    recUniq ρ f ϕ fβ (⟦bind⟧ M N ρ' i) =
      isProp→PathP
        (λ i → isSetX (f (⟦bind⟧ M N ρ' i)) (rec ρ (⟦bind⟧ M N ρ' i)))
        (uniqSub ρ f ϕ (λ w → ⟦ N w ⟧ ρ')
          (λ w → uniqSub ρ f ϕ ρ' (λ u → recUniq ρ f ϕ fβ (ρ' u)) (N w)) M)
        (uniqSub ρ f ϕ ρ' (λ u → recUniq ρ f ϕ fβ (ρ' u)) (bind N M)) i
    recUniq ρ f ϕ fβ (eqn e ρ' i) =
      isProp→PathP (λ i → isSetX (f (eqn e ρ' i)) (rec ρ (eqn e ρ' i)))
        (uniqSub ρ f ϕ ρ' (λ w → recUniq ρ f ϕ fβ (ρ' w)) (E.lhs e))
        (uniqSub ρ f ϕ ρ' (λ w → recUniq ρ f ϕ fβ (ρ' w)) (E.rhs e)) i
    recUniq ρ f ϕ fβ (trunc x y p q i j) =
      isProp→SquareP
        (λ i j → isSetX (f (trunc x y p q i j)) (rec ρ (trunc x y p q i j)))
        (λ _ → recUniq ρ f ϕ fβ x) (λ _ → recUniq ρ f ϕ fβ y)
        (λ k → recUniq ρ f ϕ fβ (p k)) (λ k → recUniq ρ f ϕ fβ (q k)) i j
