-- Binary logical relations between models of a many-sorted theory, and
-- the ABSTRACTION THEOREM.
--
-- A displayed model over a model `M` is a logical *predicate* on `M`,
-- and `Displayed.Elim.elim` is unary parametricity.  A logical
-- *relation* between `M` and `N` is the same thing over their PRODUCT,
-- so nothing new has to be built: binary parametricity is the unary
-- eliminator instantiated at `M ×Mod N`, reindexed along the pairing of
-- the two interpretations.
module Cubical.Algebra.Theory.Sorted.Displayed.Relation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category

open import Cubical.Algebra.Theory.Sorted
  using (SortedSig; SortedEqns; Tm; Ops; TmRec; MOD; ModHom)
open import Cubical.Algebra.Theory.Sorted.Product
  using (prodMod; pairMod)
open import Cubical.Algebra.Theory.Sorted.Displayed.Base
  using (SortedSigᴰ; Tmᴰ; Opsᶠᴰ; TmRecᴰ; Modelᴰˢ; UnitSigᴰ; UnitSection)
open import Cubical.Algebra.Theory.Sorted.Displayed.Terminal
  using (reindexMod; 1Mod; isTerminal1Mod)
open import Cubical.Algebra.Theory.Sorted.Closing
  using (FreeModel; FreeOb; gen; UPMod; ℓClosing)
open import Cubical.Algebra.Theory.Sorted.Displayed.Elim
  using (elim)

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX ℓR ℓO : Level

open SortedSig
open SortedEqns
open SortedSigᴰ
open Modelᴰˢ

-- ------------------------------------------------------------------
-- Relations
-- ------------------------------------------------------------------

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  {ℓX : Level} (M N : Category.ob (MOD σeq ℓX)) where

  X : S → Type ℓX
  X s = ⟨ M .fst s ⟩

  Y : S → Type ℓX
  Y s = ⟨ N .fst s ⟩

  Prod : Category.ob (MOD σeq ℓX)
  Prod = prodMod σeq M N

  -- No displayed SORTS: a relation relates elements at a common sort,
  -- so `Sortᴰ s = Unit`.  Displayed sorts would be a relation between
  -- *sorts* as well, which is a different (and coarser) notion.
  Rel : (ℓR : Level) → Type _
  Rel ℓR = Modelᴰˢ σeq Prod UnitSigᴰ ℓR

  -- what a relation relates
  relOf : Rel ℓR → (s : S) → X s → Y s → hSet ℓR
  relOf R s x y = R .carrierᴰ s tt (x , y)

  -- ----------------------------------------------------------------
  -- The same data, read as a relation
  -- ----------------------------------------------------------------
  --
  -- `relOps` is the closure condition, forded in BOTH components; it is
  -- the only field one ever writes by hand.  `relSat` says the relation
  -- respects the equations; it is `satᴰ` verbatim and is automatic when
  -- the relation is prop-valued (`propRel` below).
  record LogicalRelation (ℓR : Level)
    : Type (ℓ-max (ℓ-max (ℓ-max ℓS ℓ) (ℓ-max ℓ' ℓ''))
            (ℓ-max ℓv (ℓ-max ℓX (ℓ-suc ℓR)))) where
    field
      rel : (s : S) → X s → Y s → hSet ℓR

    relCarrier : (s : S) → Unit → ⟨ Prod .fst s ⟩ → hSet ℓR
    relCarrier s _ p = rel s (p .fst) (p .snd)

    relTy : (s : S) → Unit → ⟨ Prod .fst s ⟩ → Type ℓR
    relTy s u p = ⟨ relCarrier s u p ⟩

    field
      relOps : (o : σ .ops)
        (x : (a : σ .arities o) → X (σ .sortOf o a))
        (y : (a : σ .arities o) → Y (σ .sortOf o a))
        (xy : (a : σ .arities o) → ⟨ rel (σ .sortOf o a) (x a) (y a) ⟩)
        (u : X (σ .resultSort o)) (v : Y (σ .resultSort o))
        → u ≡ M .snd .fst o x → v ≡ N .snd .fst o y
        → ⟨ rel (σ .resultSort o) u v ⟩

    relOpsᶠ : Opsᶠᴰ UnitSigᴰ (λ s → ⟨ Prod .fst s ⟩) (Prod .snd .fst) relTy
    relOpsᶠ o i x xᴰ y eq =
      relOps o (λ a → x a .fst) (λ a → x a .snd) xᴰ
        (y .fst) (y .snd) (cong fst eq) (cong snd eq)

    field
      relSat : (e : σeq .eqns)
        (vsᴰ : (v : σeq .vars e) → Unit) (sᴰ : Unit)
        (L : Tmᴰ UnitSigᴰ vsᴰ sᴰ (σeq .lhs e))
        (R : Tmᴰ UnitSigᴰ vsᴰ sᴰ (σeq .rhs e))
        (ρ : (v : σeq .vars e) → ⟨ Prod .fst (σeq .varSort e v) ⟩)
        (ρᴰ : (v : σeq .vars e)
            → relTy (σeq .varSort e v) (vsᴰ v) (ρ v))
        → PathP (λ i → relTy (σeq .eqnSort e) sᴰ (Prod .snd .snd e ρ i))
            (TmRecᴰ UnitSigᴰ (λ s → ⟨ Prod .fst s ⟩) (Prod .snd .fst)
              relTy relOpsᶠ ρᴰ L)
            (TmRecᴰ UnitSigᴰ (λ s → ⟨ Prod .fst s ⟩) (Prod .snd .fst)
              relTy relOpsᶠ ρᴰ R)

  open LogicalRelation

  -- Currying and `Unit`/`Σ` eta only: BOTH round trips are `refl`.
  LogicalRelationIso : Iso (LogicalRelation ℓR) (Rel ℓR)
  LogicalRelationIso .Iso.fun R .carrierᴰ = relCarrier R
  LogicalRelationIso .Iso.fun R .opsᴰ = relOpsᶠ R
  LogicalRelationIso .Iso.fun R .satᴰ = relSat R
  LogicalRelationIso .Iso.inv Rᴰ .rel s x y = Rᴰ .carrierᴰ s tt (x , y)
  LogicalRelationIso .Iso.inv Rᴰ .relOps o x y xy u v p q =
    Rᴰ .opsᴰ o tt (λ a → x a , y a) xy (u , v) (ΣPathP (p , q))
  LogicalRelationIso .Iso.inv Rᴰ .relSat = Rᴰ .satᴰ
  LogicalRelationIso .Iso.sec _ = refl
  LogicalRelationIso .Iso.ret _ = refl

  mkRel : LogicalRelation ℓR → Rel ℓR
  mkRel = LogicalRelationIso .Iso.fun

  -- For a PROP-valued relation the equations are automatic, so all that
  -- is owed is closure under the operations -- and the fords can be
  -- discharged by `subst2`, since there is nothing to cohere.
  propRel : (P : (s : S) → X s → Y s → hProp ℓR)
    → ( (o : σ .ops)
        (x : (a : σ .arities o) → X (σ .sortOf o a))
        (y : (a : σ .arities o) → Y (σ .sortOf o a))
      → ((a : σ .arities o) → ⟨ P (σ .sortOf o a) (x a) (y a) ⟩)
      → ⟨ P (σ .resultSort o) (M .snd .fst o x) (N .snd .fst o y) ⟩ )
    → LogicalRelation ℓR
  propRel P clos .rel s x y = ⟨ P s x y ⟩ , isProp→isSet (P s x y .snd)
  propRel P clos .relOps o x y xy u v p q =
    subst2 (λ a b → ⟨ P (σ .resultSort o) a b ⟩) (sym p) (sym q)
      (clos o x y xy)
  propRel P clos .relSat e vsᴰ sᴰ L R ρ ρᴰ =
    isProp→PathP (λ i → P (σeq .eqnSort e) _ _ .snd) _ _

  -- The graph of a homomorphism is a logical relation.  This is the
  -- supply of relations that makes representation independence bite.
  graphRel : ModHom σeq ℓX M N → Rel ℓX
  graphRel h = mkRel (propRel
    (λ s x y → (h .fst s x ≡ y) , N .fst s .snd _ _)
    (λ o x y xy →
      h .snd .fst o x (M .snd .fst o x) refl
      ∙ cong (N .snd .fst o) (funExt xy)))

-- ------------------------------------------------------------------
-- THE ABSTRACTION THEOREM
-- ------------------------------------------------------------------
--
-- Fix a relation `R` between `M` and `N` and a pair of interpretations
-- of the generators that are `R`-related.  Then the interpretations of
-- EVERY term are `R`-related.  The proof is not an induction over
-- syntax: `pairMod` is a homomorphism into `M ×Mod N`, reindexing `R`
-- along it is a displayed model over the free model, and `elim` -- the
-- splitting of `∫π` forced by freeness -- is the section.

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  (V : Type ℓv) (vs : V → S) where

  private
    ℓC = ℓClosing ℓS ℓ ℓ' ℓ'' ℓv

    F : Category.ob (MOD σeq ℓC)
    F = FreeOb σeq V vs

  module _ (M N : Category.ob (MOD σeq ℓC))
    (ρM : (v : V) → ⟨ M .fst (vs v) ⟩)
    (ρN : (v : V) → ⟨ N .fst (vs v) ⟩) where

    private
      hM : ModHom σeq ℓC F M
      hM = Iso.inv (UPMod σeq V vs M) ρM

      hN : ModHom σeq ℓC F N
      hN = Iso.inv (UPMod σeq V vs N) ρN

    -- the unique interpretations extending `ρM` and `ρN`
    ⟦_⟧M : {s : S} → FreeModel σeq V vs s → ⟨ M .fst s ⟩
    ⟦_⟧M {s} = hM .fst s

    ⟦_⟧N : {s : S} → FreeModel σeq V vs s → ⟨ N .fst s ⟩
    ⟦_⟧N {s} = hN .fst s

    module _ (R : Rel σeq M N ℓC)
      (related : (v : V) → ⟨ relOf σeq M N R (vs v) (ρM v) (ρN v) ⟩)
      where

      private
        -- `{M}`/`{N}` must be pinned: `ModHom` is a `Σ` and does not
        -- mention its endpoints.
        Rᴰ : Modelᴰˢ σeq F UnitSigᴰ ℓC
        Rᴰ = reindexMod σeq {ℓX = ℓC} UnitSigᴰ {ℓXᴰ = ℓC}
               {M = F} {N = Prod σeq M N}
               (pairMod σeq M N F hM hN) R

      abstraction : (s : S) (t : FreeModel σeq V vs s)
        → ⟨ relOf σeq M N R s ⟦ t ⟧M ⟦ t ⟧N ⟩
      abstraction = elim σeq V vs UnitSigᴰ Rᴰ UnitSection related

      -- REPRESENTATION INDEPENDENCE.  Any observation of the two
      -- models that the relation respects agrees on every term: a
      -- client written in the theory cannot tell `M` from `N`.
      observation : {O : Type ℓO} (s : S)
        (obsM : ⟨ M .fst s ⟩ → O) (obsN : ⟨ N .fst s ⟩ → O)
        (adequate : (x : ⟨ M .fst s ⟩) (y : ⟨ N .fst s ⟩)
                  → ⟨ relOf σeq M N R s x y ⟩ → obsM x ≡ obsN y)
        (t : FreeModel σeq V vs s)
        → obsM ⟦ t ⟧M ≡ obsN ⟦ t ⟧N
      observation s obsM obsN adequate t =
        adequate ⟦ t ⟧M ⟦ t ⟧N (abstraction s t)

    -- The sharp special case: a homomorphism `h` whose graph relates
    -- the generators commutes with the interpretation of every term.
    -- This is the abstraction theorem at `graphRel`; nothing else is
    -- used, in particular no induction over `FreeModel`.
    homPreserves : (h : ModHom σeq ℓC M N)
      → ((v : V) → h .fst (vs v) (ρM v) ≡ ρN v)
      → (s : S) (t : FreeModel σeq V vs s) → h .fst s ⟦ t ⟧M ≡ ⟦ t ⟧N
    homPreserves h compat = abstraction (graphRel σeq M N h) compat

-- ------------------------------------------------------------------
-- Closed terms
-- ------------------------------------------------------------------
--
-- `V := ⊥*` is the free model on no generators, i.e. the INITIAL model.
-- Its elements are the closed terms, and there is nothing to assume
-- about generators, so the abstraction theorem applies to every
-- relation whatsoever.

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  where

  private
    ℓC = ℓClosing ℓS ℓ ℓ' ℓ'' ℓv

  -- not private: it appears in the types below, so a caller has to be
  -- able to name the very same absurd function
  noVar : ⊥* {ℓv} → S
  noVar ()

  module _ (M N : Category.ob (MOD σeq ℓC)) (R : Rel σeq M N ℓC) where

    closedM : {s : S} → FreeModel σeq (⊥* {ℓv}) noVar s → ⟨ M .fst s ⟩
    closedM = ⟦_⟧M σeq (⊥* {ℓv}) noVar M N (λ ()) (λ ())

    closedN : {s : S} → FreeModel σeq (⊥* {ℓv}) noVar s → ⟨ N .fst s ⟩
    closedN = ⟦_⟧N σeq (⊥* {ℓv}) noVar M N (λ ()) (λ ())

    closedRelated : (s : S) (t : FreeModel σeq (⊥* {ℓv}) noVar s)
      → ⟨ relOf σeq M N R s (closedM t) (closedN t) ⟩
    closedRelated =
      abstraction σeq (⊥* {ℓv}) noVar M N (λ ()) (λ ()) R (λ ())

    -- No closed term distinguishes `M` from `N` under any observation
    -- the relation respects.
    closedIndistinguishable : {O : Type ℓO} (s : S)
      (obsM : ⟨ M .fst s ⟩ → O) (obsN : ⟨ N .fst s ⟩ → O)
      → ((x : ⟨ M .fst s ⟩) (y : ⟨ N .fst s ⟩)
         → ⟨ relOf σeq M N R s x y ⟩ → obsM x ≡ obsN y)
      → (t : FreeModel σeq (⊥* {ℓv}) noVar s)
      → obsM (closedM t) ≡ obsN (closedN t)
    closedIndistinguishable =
      observation σeq (⊥* {ℓv}) noVar M N (λ ()) (λ ()) R (λ ())

-- ------------------------------------------------------------------
-- The unary case is `N := 1Mod`: isomorphic, NOT definitional
-- ------------------------------------------------------------------
--
-- A relation with the terminal model is a predicate, and the passage is
-- exactly reindexing along `⟨ id , ! ⟩ : M → M ×Mod 1Mod`.  The CARRIER
-- and the OPERATIONS transfer on the nose (`unaryCarrier`, `unaryOps`
-- are `refl`) -- that is the ford paying off, since `reindexMod` never
-- transports those two.  The EQUATIONS do not: the base path of the
-- product's `sat×` is `satM` conjugated by `TmRec×`, not `satM`, and
-- `reindexMod`'s `sat*` moves the displayed equation across `TmRecHom`
-- by a chain of `subst`s.  Same verdict, and the same cause, as
-- `Displayed.Terminal`'s `ObIso`.

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  {ℓX : Level} (M : Category.ob (MOD σeq ℓX)) where

  1M : Category.ob (MOD σeq ℓX)
  1M = 1Mod σeq ℓX

  toProd : ModHom σeq ℓX M (Prod σeq M 1M)
  toProd = pairMod σeq M 1M M
    (Category.id (MOD σeq ℓX) {x = M}) (isTerminal1Mod σeq ℓX M .fst)

  unaryFromBinary : {ℓR : Level}
    → Rel σeq M 1M ℓR → Modelᴰˢ σeq M UnitSigᴰ ℓR
  unaryFromBinary {ℓR = ℓR} R =
    reindexMod σeq {ℓX = ℓX} UnitSigᴰ {ℓXᴰ = ℓR}
      {M = M} {N = Prod σeq M 1M} toProd R

  unaryCarrier : {ℓR : Level} (R : Rel σeq M 1M ℓR)
    (s : S) (u : Unit) (x : ⟨ M .fst s ⟩)
    → unaryFromBinary R .carrierᴰ s u x ≡ R .carrierᴰ s u (x , tt*)
  unaryCarrier R s u x = refl

  unaryOps : {ℓR : Level} (R : Rel σeq M 1M ℓR) (o : σ .ops) (i : Unit)
    (x : (a : σ .arities o) → ⟨ M .fst (σ .sortOf o a) ⟩)
    (xᴰ : (a : σ .arities o)
        → ⟨ R .carrierᴰ (σ .sortOf o a) tt (x a , tt*) ⟩)
    (y : ⟨ M .fst (σ .resultSort o) ⟩) (eq : y ≡ M .snd .fst o x)
    → unaryFromBinary R .opsᴰ o i x xᴰ y eq
      ≡ R .opsᴰ o i (λ a → x a , tt*) xᴰ (y , tt*)
          (toProd .snd .fst o x y eq)
  unaryOps R o i x xᴰ y eq = refl
