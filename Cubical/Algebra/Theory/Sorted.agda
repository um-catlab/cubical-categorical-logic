-- Multi-sorted algebraic theories, as a tower of displayed categories.
--
--     FAM S ℓX        S-indexed families of sets: the carriers
--       ↑ ALGᴰ        interpretation of the operations
--       ↑ EQNSᴰ       the equations hold (prop-valued: a full subcategory)
--
-- `S = Unit` recovers the single-sorted case; `S = Ob × Ob` gives
-- morphism theories, so `MOD` is categories with object set Ob.
--
-- Arguments carry their sorts (`sortOf`) rather than being fibred over
-- S.  Composition has arguments at *different* sorts, and a fibred
-- family `arities o : S → Type` can only say that with paths, which
-- would put a transport at every use site.
module Cubical.Algebra.Theory.Sorted where

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
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.TotalCategory

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX : Level

record SortedSig (S : Type ℓS) ℓ ℓ'
  : Type (ℓ-max ℓS (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))) where
  field
    ops : Type ℓ
    arities : ops → Type ℓ'
    sortOf : (o : ops) → arities o → S
    resultSort : ops → S

open SortedSig

module _ {S : Type ℓS} (σ : SortedSig S ℓ ℓ') where
  data Tm (V : Type ℓv) (vs : V → S)
    : S → Type (ℓ-max (ℓ-max ℓS ℓ) (ℓ-max ℓ' ℓv)) where
    var : (v : V) → Tm V vs (vs v)
    node : (o : σ .ops)
      → ((a : σ .arities o) → Tm V vs (σ .sortOf o a))
      → Tm V vs (σ .resultSort o)

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} where
  -- an interpretation of the operations on an S-indexed family
  Ops : (S → Type ℓX) → Type _
  Ops X = (o : σ .ops)
    → ((a : σ .arities o) → X (σ .sortOf o a)) → X (σ .resultSort o)

  TmRec : (X : S → Type ℓX) (α : Ops X)
    {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v))
    {s : S} → Tm σ V vs s → X s
  TmRec X α ρ (var v) = ρ v
  TmRec X α ρ (node o ts) = α o (λ a → TmRec X α ρ (ts a))

record SortedEqns {S : Type ℓS} (σ : SortedSig S ℓ ℓ') ℓ'' ℓv
  : Type (ℓ-max (ℓ-max ℓS ℓ) (ℓ-max (ℓ-max ℓ' (ℓ-suc ℓ'')) (ℓ-suc ℓv))) where
  field
    eqns : Type ℓ''
    eqnSort : eqns → S
    vars : eqns → Type ℓv
    varSort : (e : eqns) → vars e → S
    lhs rhs : (e : eqns) → Tm σ (vars e) (varSort e) (eqnSort e)

open SortedEqns

-- the base of the tower: S-indexed families of sets
FAM : (S : Type ℓS) (ℓX : Level)
  → Category (ℓ-max ℓS (ℓ-suc ℓX)) (ℓ-max ℓS ℓX)
FAM S ℓX .Category.ob = S → hSet ℓX
FAM S ℓX .Category.Hom[_,_] X Y = (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩
FAM S ℓX .Category.id s x = x
FAM S ℓX .Category._⋆_ f g s x = g s (f s x)
FAM S ℓX .Category.⋆IdL f = refl
FAM S ℓX .Category.⋆IdR f = refl
FAM S ℓX .Category.⋆Assoc f g h = refl
FAM S ℓX .Category.isSetHom {y = Y} =
  isSetΠ2 (λ s _ → Y s .snd)

module _ {S : Type ℓS} (σ : SortedSig S ℓ ℓ') (ℓX : Level) where

  -- layer one: the operations, with the forded homomorphism condition
  ALGᴰ : Categoryᴰ (FAM S ℓX) _ _
  ALGᴰ .Categoryᴰ.ob[_] X = Ops {σ = σ} (λ s → ⟨ X s ⟩)
  ALGᴰ .Categoryᴰ.Hom[_][_,_] {x = X} {y = Y} f α β =
    (o : σ .ops) (x : (a : σ .arities o) → ⟨ X (σ .sortOf o a) ⟩)
    (y : ⟨ X (σ .resultSort o) ⟩) → y ≡ α o x
    → f (σ .resultSort o) y ≡ β o (λ a → f (σ .sortOf o a) (x a))
  ALGᴰ .Categoryᴰ.idᴰ o x y eq = eq
  ALGᴰ .Categoryᴰ._⋆ᴰ_ {f = f} ϕ ψ o x y eq =
    ψ o (λ a → f (σ .sortOf o a) (x a)) (f (σ .resultSort o) y) (ϕ o x y eq)
  ALGᴰ .Categoryᴰ.⋆IdLᴰ ϕ = refl
  ALGᴰ .Categoryᴰ.⋆IdRᴰ ϕ = refl
  ALGᴰ .Categoryᴰ.⋆Assocᴰ ϕ ψ χ = refl
  ALGᴰ .Categoryᴰ.isSetHomᴰ {y = Y} =
    isSetΠ3 (λ o x y → isSet→ (isProp→isSet (Y _ .snd _ _)))

  ALG : Category _ _
  ALG = ∫C ALGᴰ

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' ℓv) (ℓX : Level) where

  -- layer two: the equations.  Prop-valued objects, trivial homs, so
  -- this is a full subcategory inclusion.
  EQNSᴰ : Categoryᴰ (ALG σ ℓX) _ _
  EQNSᴰ .Categoryᴰ.ob[_] (X , α) =
    (e : σeq .eqns) (ρ : (v : σeq .vars e) → ⟨ X (σeq .varSort e v) ⟩)
    → TmRec (λ s → ⟨ X s ⟩) α ρ (σeq .lhs e)
      ≡ TmRec (λ s → ⟨ X s ⟩) α ρ (σeq .rhs e)
  EQNSᴰ .Categoryᴰ.Hom[_][_,_] _ _ _ = Unit* {ℓ-zero}
  EQNSᴰ .Categoryᴰ.idᴰ = tt*
  EQNSᴰ .Categoryᴰ._⋆ᴰ_ _ _ = tt*
  EQNSᴰ .Categoryᴰ.⋆IdLᴰ _ = refl
  EQNSᴰ .Categoryᴰ.⋆IdRᴰ _ = refl
  EQNSᴰ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
  EQNSᴰ .Categoryᴰ.isSetHomᴰ = isProp→isSet (λ _ _ → refl)

  MODᴰ : Categoryᴰ (FAM S ℓX) _ _
  MODᴰ = ∫Cᴰ (ALGᴰ σ ℓX) EQNSᴰ

  MOD : Category _ _
  MOD = ∫C MODᴰ

  -- a homomorphism of models.  `ModHom σeq ℓX M N` is
  -- what this unfolds to, and it appears often enough to deserve a name.
  ModHom : (M N : Category.ob MOD) → Type _
  ModHom M N = MOD [ M , N ]

-- The free model.  `node` is a constructor in its own right -- with
-- `sortOf` it cannot be derived as `⟦ node o var ⟧` without a transport
-- -- and `⟦node⟧` relates it to explicit substitution.  That clause of
-- `rec` is `refl`, which is what removes the need for a substitution law.
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

    -- `⊥` and `Bool` arities have no definitional η, so the selector
    -- `TmRec` builds is never syntactically the one a named term builder
    -- builds.  Every instance was writing this bridge per operation.
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
