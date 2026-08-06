-- The terminal model, and the fibre of `MODᴰᴰ` over it.
--
-- The design question this file settles: is a model of `σeq` the same
-- thing as a *vertical* displayed model over the terminal model?  If so,
-- `Modelᴰˢ` would be the only primitive notion and `MOD` a derived one.
--
-- VERDICT: isomorphic, not definitionally equal.
--
--   * Objects are NOT definitionally equal.  `Category.ob Fib` is the
--     record `Modelᴰˢ σeq 1Mod UnitSigᴰ ℓXᴰ`, whose carrier field has
--     type `(s : S) → Unit → Unit* → hSet ℓXᴰ`; `Category.ob (MOD σeq
--     ℓXᴰ)` is a nested `Σ` whose first component has type
--     `S → hSet ℓXᴰ`.  A record is never a `Σ`.  See `ObIso`.
--
--   * The *carrier* and *operations* components do round-trip by `refl`
--     (`toFromCarrier`, `toFromOps`, `fromToCarrier`, `fromToOps`):
--     `Unit`, `Unit*` and paths in `Unit*` all have definitional eta, so
--     the extra arguments are erased judgementally.  Only the
--     *equations* component fails, because `satᴰ` is stated at `TmRecᴰ`
--     over a displayed typing derivation while `sat` is stated at
--     `TmRec`, and `tmLem` relating them is a `cong`, not `refl`.  Both
--     are paths in a set, so the failure is a proposition
--     (`toFromMod`, `fromToMod`).
--
--   * Homs are NOT definitionally equal either -- the fibre's homs carry
--     two extra `Unit`/`Unit*` arguments -- but the comparison is eta,
--     so unlike the objects BOTH round trips are `refl` (`HomIso`).
--
--   * `MOD` is strict at the identity (`MOD⋆IdLrefl`, `MODid⋆id`), so
--     `⋆ᴰ` already lands in `Hom[ id ]` and the comparison is functorial
--     by `refl` when composition is taken to be `⋆ᴰ` (`homIsoSeqᴰ`).
--     Against the generic fibre `Fibers.v[_]`, whose `_⋆_` inserts a
--     `reind`, `F-seq` is not `refl` (`⋆ⱽ≡⋆ᴰ`, `Compare`).
--
-- The last section answers a separate question in the affirmative:
-- `MODᴰᴰ` IS a fibration (`reindexMod`, `cartπ`, `cartβ`, `cartIso`).
-- Reindexing the carrier and the operations along a homomorphism is
-- transport-free, exactly because `opsᴰ` is forded; only `satᴰ` costs a
-- transport argument.  The cartesian property is then degenerate:
-- `MODᴰᴰ [ g ⋆ hom ][ Lᴰ , Nᴰ ]` and `MODᴰᴰ [ g ][ Lᴰ , reindexMod ]`
-- are definitionally the SAME type and `_⋆ᴰ cartπ` is the identity
-- function, so every component of the universal property is `refl`.
module Cubical.Algebra.Theory.Sorted.Displayed.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.Fiber using (module Fibers)

open import Cubical.Algebra.Theory.Sorted
  using (SortedSig; SortedEqns; Tm; var; node; Ops; TmRec; MOD;
         ModHom)
open import Cubical.Algebra.Theory.Sorted.Displayed.Base
  using (SortedSigᴰ; Tmᴰ; varᴰ; nodeᴰ; Modelᴰˢ; MODᴰᴰ; UnitSigᴰ;
         Opsᶠᴰ; TmRecᴰ; unfordᴰ)

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX ℓXᴰ ℓSᴰ ℓi : Level

open SortedSig
open SortedEqns
open SortedSigᴰ
open Modelᴰˢ

-- ------------------------------------------------------------------
-- The terminal model
-- ------------------------------------------------------------------
--
-- Every carrier is `Unit*`, so every operation is `tt*` and, because
-- `Unit*` has definitional eta, every equation holds by `refl` -- not by
-- `isPropUnit*`.  That matters below: it is what makes the displayed
-- equations of a displayed model over `1Mod` plain paths, not `PathP`s.

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' ℓv) (ℓX : Level) where

  1Mod : Category.ob (MOD σeq ℓX)
  1Mod = (λ _ → Unit* , isSetUnit*) , (λ _ _ → tt*) , (λ _ _ → refl)

  isTerminal1Mod : isTerminal (MOD σeq ℓX) 1Mod
  isTerminal1Mod M =
    isContrΣ (isContrΠ (λ _ → isContrΠ (λ _ → isContrUnit*)))
      (λ f → isContrΣ
        (isContrΠ (λ o → isContrΠ (λ x → isContrΠ (λ y → isContrΠ
          (λ eq → isContr→isContrPath isContrUnit* _ _)))))
        (λ _ → isContrUnit*))

  Terminal1Mod : Terminal (MOD σeq ℓX)
  Terminal1Mod = 1Mod , isTerminal1Mod

-- ------------------------------------------------------------------
-- The fibre of `MODᴰᴰ` over the terminal model
-- ------------------------------------------------------------------
--
-- `UnitSigᴰ` is the displayed signature with trivial displayed sorts;
-- that is the case in which a displayed model is a bare family over the
-- base carrier, so it is the case in which the claim could hold.

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' ℓv) (ℓXᴰ : Level) where

  private
    MODᴰᴰ1 : Categoryᴰ (MOD σeq ℓ-zero) _ _
    MODᴰᴰ1 = MODᴰᴰ σeq {ℓX = ℓ-zero} (UnitSigᴰ {σ = σ}) {ℓXᴰ = ℓXᴰ}

  Fib : Category _ _
  Fib = Fibers.v[_] MODᴰᴰ1 (1Mod σeq ℓ-zero)

  -- Over `UnitSigᴰ` every term has a displayed typing, and by eta on
  -- `Unit` it is one at every displayed sort.
  canonTmᴰ : {V : Type ℓv} {vs : V → S} {vsᴰ : (v : V) → Unit}
    {s : S} {sᴰ : Unit} (N : Tm σ V vs s)
    → Tmᴰ (UnitSigᴰ {σ = σ}) vsᴰ sᴰ N
  canonTmᴰ (var v) = varᴰ v
  canonTmᴰ (node o ts) = nodeᴰ o tt ts (λ a → canonTmᴰ (ts a))

  -- Both directions of the comparison need the same bridging lemma, so
  -- it is stated for a bare displayed carrier + forded displayed
  -- operations rather than for a `Modelᴰˢ`.
  module _ (Yᴰ : (s : S) → Unit → Unit* {ℓ-zero} → Type ℓXᴰ)
    (αᴰ : Opsᶠᴰ (UnitSigᴰ {σ = σ}) (λ _ → Unit*) (λ _ _ → tt*) Yᴰ) where

    Y : S → Type ℓXᴰ
    Y s = Yᴰ s tt tt*

    β : Ops {σ = σ} Y
    β o xᴰ = αᴰ o tt (λ _ → tt*) xᴰ tt* refl

    -- THE one place where the two presentations genuinely differ:
    -- `TmRecᴰ` recurses on a displayed typing derivation, `TmRec` on the
    -- term.  The `var` case is `refl`; the `node` case is a `cong`.
    tmLem : {V : Type ℓv} {vs : V → S} {vsᴰ : (v : V) → Unit}
      (ρᴰ : (v : V) → Y (vs v))
      {s : S} {sᴰ : Unit} {N : Tm σ V vs s}
      (Nᴰ : Tmᴰ (UnitSigᴰ {σ = σ}) vsᴰ sᴰ N)
      → TmRecᴰ (UnitSigᴰ {σ = σ}) (λ _ → Unit*) (λ _ _ → tt*)
          Yᴰ αᴰ {ρ = λ _ → tt*} ρᴰ Nᴰ
        ≡ TmRec Y β ρᴰ N
    tmLem ρᴰ (varᴰ v) = refl
    tmLem ρᴰ (nodeᴰ o i ts tsᴰ) =
      cong (λ g → αᴰ o tt (λ _ → tt*) g tt* refl)
        (funExt (λ a → tmLem ρᴰ (tsᴰ a)))

  module _ (Mᴰ : Modelᴰˢ σeq (1Mod σeq ℓ-zero) (UnitSigᴰ {σ = σ}) ℓXᴰ)
    where

    toMod : Category.ob (MOD σeq ℓXᴰ)
    toMod = (λ s → Mᴰ .carrierᴰ s tt tt*) , β (Xᴰ Mᴰ) (Mᴰ .opsᴰ)
      , λ e ρᴰ →
          sym (tmLem (Xᴰ Mᴰ) (Mᴰ .opsᴰ) ρᴰ (canonTmᴰ (σeq .lhs e)))
          ∙ Mᴰ .satᴰ e (λ _ → tt) tt
              (canonTmᴰ (σeq .lhs e)) (canonTmᴰ (σeq .rhs e))
              (λ _ → tt*) ρᴰ
          ∙ tmLem (Xᴰ Mᴰ) (Mᴰ .opsᴰ) ρᴰ (canonTmᴰ (σeq .rhs e))

  module _ (M : Category.ob (MOD σeq ℓXᴰ)) where
    private
      Yᴰ' : (s : S) → Unit → Unit* {ℓ-zero} → Type ℓXᴰ
      Yᴰ' s _ _ = ⟨ M .fst s ⟩

      αᴰ' : Opsᶠᴰ (UnitSigᴰ {σ = σ}) (λ _ → Unit*) (λ _ _ → tt*) Yᴰ'
      αᴰ' o i x xᴰ y eq = M .snd .fst o xᴰ

    fromMod : Modelᴰˢ σeq (1Mod σeq ℓ-zero) (UnitSigᴰ {σ = σ}) ℓXᴰ
    fromMod .carrierᴰ s _ _ = M .fst s
    fromMod .opsᴰ = αᴰ'
    fromMod .satᴰ e vsᴰ sᴰ L R ρ ρᴰ =
      tmLem Yᴰ' αᴰ' ρᴰ L ∙ M .snd .snd e ρᴰ ∙ sym (tmLem Yᴰ' αᴰ' ρᴰ R)

  -- ----------------------------------------------------------------
  -- MEASUREMENT, objects
  -- ----------------------------------------------------------------
  --
  --   obTest : Category.ob Fib ≡ Category.ob (MOD σeq ℓXᴰ)
  --   obTest = refl
  --
  -- is REJECTED (the levels do agree, so the statement is well formed):
  --
  --   The terms
  --     Modelᴰˢ σeq (1Mod σeq ℓ-zero) UnitSigᴰ ℓXᴰ
  --   and
  --     Σ (Cubical.Algebra.Theory.Sorted.FAM S ℓXᴰ .Category.ob)
  --     Categoryᴰ.ob[ Cubical.Algebra.Theory.Sorted.MODᴰ σeq ℓXᴰ ]
  --   are not equal at type Type ...
  --
  -- The carrier and the operations do survive both round trips on the
  -- nose, though.

  toFromCarrier : (M : Category.ob (MOD σeq ℓXᴰ))
    → toMod (fromMod M) .fst ≡ M .fst
  toFromCarrier M = refl

  toFromOps : (M : Category.ob (MOD σeq ℓXᴰ))
    → toMod (fromMod M) .snd .fst ≡ M .snd .fst
  toFromOps M = refl

  fromToCarrier : (Mᴰ : Category.ob Fib)
    → fromMod (toMod Mᴰ) .carrierᴰ ≡ Mᴰ .carrierᴰ
  fromToCarrier Mᴰ = refl

  fromToOps : (Mᴰ : Category.ob Fib)
    → fromMod (toMod Mᴰ) .opsᴰ ≡ Mᴰ .opsᴰ
  fromToOps Mᴰ = refl

  -- Only the equations component obstructs `refl`.  On whole objects,
  -- `toMod (fromMod M) ≡ M` by `refl` is REJECTED with
  --
  --   The terms
  --     hcomp (doubleComp-faces ...) ...
  --   and
  --     M .snd .snd e ρ i
  --   are not equal at type fst (M .fst (σeq .eqnSort e))
  --
  -- i.e. the `∙`-chain through `tmLem` against the original proof.  It
  -- is a path in a set, hence a proposition.

  toFromMod : (M : Category.ob (MOD σeq ℓXᴰ)) → toMod (fromMod M) ≡ M
  toFromMod M = ΣPathP (refl , ΣPathP (refl ,
    isPropΠ2 (λ e ρ → M .fst (σeq .eqnSort e) .snd _ _) _ _))

  fromToMod : (Mᴰ : Category.ob Fib) → fromMod (toMod Mᴰ) ≡ Mᴰ
  fromToMod Mᴰ i .carrierᴰ = Mᴰ .carrierᴰ
  fromToMod Mᴰ i .opsᴰ = Mᴰ .opsᴰ
  fromToMod Mᴰ i .satᴰ =
    isPropΠ (λ e → isPropΠ (λ vsᴰ → isPropΠ (λ sᴰ → isPropΠ (λ L →
      isPropΠ (λ R → isPropΠ (λ ρ → isPropΠ (λ ρᴰ →
        Mᴰ .carrierᴰ (σeq .eqnSort e) sᴰ tt* .snd _ _)))))))
      (fromMod (toMod Mᴰ) .satᴰ) (Mᴰ .satᴰ) i

  ObIso : Iso (Category.ob Fib) (Category.ob (MOD σeq ℓXᴰ))
  ObIso .Iso.fun = toMod
  ObIso .Iso.inv = fromMod
  ObIso .Iso.sec = toFromMod
  ObIso .Iso.ret = fromToMod

  -- ----------------------------------------------------------------
  -- MEASUREMENT, homs
  -- ----------------------------------------------------------------
  --
  --   homTest : (Mᴰ Nᴰ : Category.ob Fib)
  --     → Fib [ Mᴰ , Nᴰ ] ≡ MOD σeq ℓXᴰ [ toMod Mᴰ , toMod Nᴰ ]
  --   homTest Mᴰ Nᴰ = refl
  --
  -- is REJECTED:
  --
  --   The types
  --     fst (Mᴰ .carrierᴰ s tt (lift tt))
  --   and
  --     Unit
  --   are not equal
  --
  -- Agda has matched the sort argument `s` of both hom types and then
  -- hit the fibre's extra displayed-sort argument `sᴰ : Unit` against
  -- the model hom's carrier argument.  The mismatch is exactly the two
  -- spurious arguments `sᴰ : Unit` and `x : Unit*`.  Deleting them is
  -- eta, so unlike the objects BOTH round trips are `refl`.

  HomIso : (Mᴰ Nᴰ : Category.ob Fib)
    → Iso (Fib [ Mᴰ , Nᴰ ]) (MOD σeq ℓXᴰ [ toMod Mᴰ , toMod Nᴰ ])
  HomIso Mᴰ Nᴰ .Iso.fun (fᴰ , ϕᴰ) =
    (λ s → fᴰ s tt tt*)
    , (λ o x y eq → ϕᴰ o tt (λ _ → tt*) x tt* refl y eq)
    , tt*
  HomIso Mᴰ Nᴰ .Iso.inv (f , ϕ , _) =
    (λ s sᴰ x → f s)
    , (λ o i x xᴰ y eq yᴰ hyp → ϕ o xᴰ yᴰ hyp)
  HomIso Mᴰ Nᴰ .Iso.sec _ = refl
  HomIso Mᴰ Nᴰ .Iso.ret _ = refl

  homIsoId : (Mᴰ : Category.ob Fib)
    → HomIso Mᴰ Mᴰ .Iso.fun (Category.id Fib {x = Mᴰ})
      ≡ Category.id (MOD σeq ℓXᴰ) {x = toMod Mᴰ}
  homIsoId Mᴰ = refl

  -- ----------------------------------------------------------------
  -- MEASUREMENT, composition
  -- ----------------------------------------------------------------
  --
  -- `MOD` is a strict category at the identity: `id ⋆ id` IS `id`, and
  -- `⋆IdL` IS `refl`.

  MODid⋆id : Category._⋆_ (MOD σeq ℓ-zero)
      {x = 1Mod σeq ℓ-zero} {y = 1Mod σeq ℓ-zero} {z = 1Mod σeq ℓ-zero}
      (Category.id (MOD σeq ℓ-zero) {x = 1Mod σeq ℓ-zero})
      (Category.id (MOD σeq ℓ-zero) {x = 1Mod σeq ℓ-zero})
    ≡ Category.id (MOD σeq ℓ-zero) {x = 1Mod σeq ℓ-zero}
  MODid⋆id = refl

  MOD⋆IdLrefl : (f : MOD σeq ℓ-zero [ 1Mod σeq ℓ-zero , 1Mod σeq ℓ-zero ])
    → Category.⋆IdL (MOD σeq ℓ-zero)
        {x = 1Mod σeq ℓ-zero} {y = 1Mod σeq ℓ-zero} f
      ≡ refl
  MOD⋆IdLrefl f = refl

  -- So `⋆ᴰ` already lands in `Hom[ id ]` with no correction, and the
  -- comparison is functorial by `refl` for THAT composition.
  homIsoSeqᴰ : (Mᴰ Nᴰ Pᴰ : Category.ob Fib)
    (fⱽ : Fib [ Mᴰ , Nᴰ ]) (gⱽ : Fib [ Nᴰ , Pᴰ ])
    → HomIso Mᴰ Pᴰ .Iso.fun
        (Categoryᴰ._⋆ᴰ_ MODᴰᴰ1 {xᴰ = Mᴰ} {yᴰ = Nᴰ} {zᴰ = Pᴰ} fⱽ gⱽ)
      ≡ Category._⋆_ (MOD σeq ℓXᴰ)
          {x = toMod Mᴰ} {y = toMod Nᴰ} {z = toMod Pᴰ}
          (HomIso Mᴰ Nᴰ .Iso.fun fⱽ) (HomIso Nᴰ Pᴰ .Iso.fun gⱽ)
  homIsoSeqᴰ _ _ _ _ _ = refl

  -- The generic fibre nevertheless composes with a `reind` along
  -- `⋆IdL`.  That `reind` is `subst _ refl`, propositional but not
  -- definitional, and it is the ONLY reason the same statement for
  -- `Category._⋆_ Fib` is REJECTED, with residual
  --
  --   Cubical.Foundations.More.depReasoning.reind
  --   (λ section → Categoryᴰ.Hom[ MODᴰᴰ1 ][ section , Mᴰ ] Pᴰ)
  --   (MOD σeq ℓ-zero .Category.⋆IdL (MOD σeq ℓ-zero .Category.id))
  --   ((MODᴰᴰ1 Categoryᴰ.⋆ᴰ fⱽ) gⱽ) .fst s tt tt* x
  --   and
  --   gⱽ .fst s tt (lift tt) (Iso.fun (HomIso Mᴰ Nᴰ) fⱽ .fst s x)
  --   are not equal

  open Fibers MODᴰᴰ1 using (rectifyOut; reind-filler⁻)

  ⋆ⱽ≡⋆ᴰ : (Mᴰ Nᴰ Pᴰ : Category.ob Fib)
    (fⱽ : Fib [ Mᴰ , Nᴰ ]) (gⱽ : Fib [ Nᴰ , Pᴰ ])
    → Category._⋆_ Fib {x = Mᴰ} {y = Nᴰ} {z = Pᴰ} fⱽ gⱽ
      ≡ Categoryᴰ._⋆ᴰ_ MODᴰᴰ1 {xᴰ = Mᴰ} {yᴰ = Nᴰ} {zᴰ = Pᴰ} fⱽ gⱽ
  ⋆ⱽ≡⋆ᴰ Mᴰ Nᴰ Pᴰ fⱽ gⱽ =
    rectifyOut {aᴰ = Mᴰ} {bᴰ = Pᴰ} {e' = refl}
      (reind-filler⁻ {aᴰ = Mᴰ} {bᴰ = Pᴰ}
        {p = Categoryᴰ._⋆ᴰ_ MODᴰᴰ1 {xᴰ = Mᴰ} {yᴰ = Nᴰ} {zᴰ = Pᴰ} fⱽ gⱽ}
        _)

  -- The comparison functor.  `F-id` is `refl`; `F-seq` is not.
  Compare : Functor Fib (MOD σeq ℓXᴰ)
  Compare .Functor.F-ob = toMod
  Compare .Functor.F-hom {x = Mᴰ} {y = Nᴰ} = HomIso Mᴰ Nᴰ .Iso.fun
  Compare .Functor.F-id {x = Mᴰ} = refl
  Compare .Functor.F-seq {x = Mᴰ} {y = Nᴰ} {z = Pᴰ} fⱽ gⱽ =
    cong (HomIso Mᴰ Pᴰ .Iso.fun) (⋆ⱽ≡⋆ᴰ Mᴰ Nᴰ Pᴰ fⱽ gⱽ)

  isFullyFaithfulCompare : Functor.isFullyFaithful Compare
  isFullyFaithfulCompare Mᴰ Nᴰ = isoToIsEquiv (HomIso Mᴰ Nᴰ)

-- ------------------------------------------------------------------
-- Is `MODᴰᴰ` a fibration?  Reindexing along a homomorphism.
-- ------------------------------------------------------------------

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  {ℓX : Level} (σᴰ : SortedSigᴰ σ ℓSᴰ ℓi) {ℓXᴰ : Level}
  {M N : Category.ob (MOD σeq ℓX)} (hom : ModHom σeq ℓX M N)
  (Nᴰ : Modelᴰˢ σeq N σᴰ ℓXᴰ) where

  private
    X : S → Type ℓX
    X s = ⟨ M .fst s ⟩

    Yb : S → Type ℓX
    Yb s = ⟨ N .fst s ⟩

    αM = M .snd .fst
    αN = N .snd .fst
    satM = M .snd .snd

    f : (s : S) → X s → Yb s
    f = hom .fst

    ϕ : (o : σ .ops) (x : (a : σ .arities o) → X (σ .sortOf o a))
        (y : X (σ .resultSort o)) → y ≡ αM o x
      → f (σ .resultSort o) y ≡ αN o (λ a → f (σ .sortOf o a) (x a))
    ϕ = hom .snd .fst

    Xᴰ* : (s : S) → σᴰ .Sortᴰ s → X s → Type ℓXᴰ
    Xᴰ* s sᴰ x = Xᴰ Nᴰ s sᴰ (f s x)

    -- The point of the ford: no `subst`, no `PathP`.  `Nᴰ .opsᴰ`
    -- accepts `f _ y` presented via the homomorphism condition.
    ops* : Opsᶠᴰ σᴰ X αM Xᴰ*
    ops* o i x xᴰ y eq =
      Nᴰ .opsᴰ o i (λ a → f (σ .sortOf o a) (x a)) xᴰ
        (f (σ .resultSort o) y) (ϕ o x y eq)

    -- `Σ[ z ] (z ≡ c)` is contractible: any two presentations of a
    -- forded result are connected.
    isContrCoSingl : {A : Type ℓX} (c : A) → isContr (Σ[ z ∈ A ] (z ≡ c))
    isContrCoSingl c .fst = c , refl
    isContrCoSingl c .snd (z , p) i = p (~ i) , λ j → p (~ i ∨ j)

    TmRecHom : {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v))
      {s : S} (t : Tm σ V vs s)
      → f s (TmRec X αM ρ t) ≡ TmRec Yb αN (λ v → f (vs v) (ρ v)) t
    TmRecHom ρ (var v) = refl
    TmRecHom ρ (node o ts) =
      ϕ o _ _ refl ∙ cong (αN o) (funExt (λ a → TmRecHom ρ (ts a)))

    TmRecHomᴰ : {V : Type ℓv} {vs : V → S}
      {vsᴰ : (v : V) → σᴰ .Sortᴰ (vs v)} {ρ : (v : V) → X (vs v)}
      (ρᴰ : (v : V) → Xᴰ* (vs v) (vsᴰ v) (ρ v))
      {s : S} {sᴰ : σᴰ .Sortᴰ s} {t : Tm σ V vs s}
      (tᴰ : Tmᴰ σᴰ vsᴰ sᴰ t)
      → PathP (λ i → Xᴰ Nᴰ s sᴰ (TmRecHom ρ t i))
          (TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ tᴰ)
          (TmRecᴰ σᴰ Yb αN (Xᴰ Nᴰ) (Nᴰ .opsᴰ)
            {ρ = λ v → f (vs v) (ρ v)} ρᴰ tᴰ)
    TmRecHomᴰ ρᴰ (varᴰ v) = refl
    TmRecHomᴰ {vs = vs} {ρ = ρ} ρᴰ (nodeᴰ o oi ts tsᴰ) =
      subst
        (λ p → PathP
          (λ i → Xᴰ Nᴰ (σ .resultSort o) (σᴰ .resSortᴰ o oi) (p i))
          (TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ (nodeᴰ o oi ts tsᴰ))
          (TmRecᴰ σᴰ Yb αN (Xᴰ Nᴰ) (Nᴰ .opsᴰ)
            {ρ = λ v → f (vs v) (ρ v)} ρᴰ (nodeᴰ o oi ts tsᴰ)))
        fix inner
      where
        x : (a : σ .arities o) → X (σ .sortOf o a)
        x a = TmRec X αM ρ (ts a)

        x'' : (a : σ .arities o) → Yb (σ .sortOf o a)
        x'' a = TmRec Yb αN (λ v → f (vs v) (ρ v)) (ts a)

        xp : (λ a → f (σ .sortOf o a) (x a)) ≡ x''
        xp = funExt (λ a → TmRecHom ρ (ts a))

        yp : PathP
               (λ i → Σ[ z ∈ Yb (σ .resultSort o) ] (z ≡ αN o (xp i)))
               (f (σ .resultSort o) (αM o x) , ϕ o x (αM o x) refl)
               (αN o x'' , refl)
        yp = isProp→PathP (λ i → isContr→isProp (isContrCoSingl _)) _ _

        inner : PathP
          (λ i → Xᴰ Nᴰ (σ .resultSort o) (σᴰ .resSortᴰ o oi) (yp i .fst))
          (TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ (nodeᴰ o oi ts tsᴰ))
          (TmRecᴰ σᴰ Yb αN (Xᴰ Nᴰ) (Nᴰ .opsᴰ)
            {ρ = λ v → f (vs v) (ρ v)} ρᴰ (nodeᴰ o oi ts tsᴰ))
        inner i =
          Nᴰ .opsᴰ o oi (xp i) (λ a → TmRecHomᴰ ρᴰ (tsᴰ a) i)
            (yp i .fst) (yp i .snd)

        fix : (λ i → yp i .fst) ≡ TmRecHom ρ (node o ts)
        fix = N .fst (σ .resultSort o) .snd _ _ _ _

    sat* : (e : σeq .eqns)
      (vsᴰ : (v : σeq .vars e) → σᴰ .Sortᴰ (σeq .varSort e v))
      (sᴰ : σᴰ .Sortᴰ (σeq .eqnSort e))
      (L : Tmᴰ σᴰ vsᴰ sᴰ (σeq .lhs e)) (R : Tmᴰ σᴰ vsᴰ sᴰ (σeq .rhs e))
      (ρ : (v : σeq .vars e) → X (σeq .varSort e v))
      (ρᴰ : (v : σeq .vars e) → Xᴰ* (σeq .varSort e v) (vsᴰ v) (ρ v))
      → PathP (λ i → Xᴰ* (σeq .eqnSort e) sᴰ (satM e ρ i))
          (TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ L)
          (TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ R)
    sat* e vsᴰ sᴰ L R ρ ρᴰ = toPathP
      ( cong (λ p → subst B p L') basefix
      ∙ substComposite B u (v ∙ sym w) L'
      ∙ cong (subst B (v ∙ sym w)) (fromPathP (TmRecHomᴰ ρᴰ L))
      ∙ substComposite B v (sym w) L''
      ∙ cong (subst B (sym w))
          (fromPathP (Nᴰ .satᴰ e vsᴰ sᴰ L R fρ ρᴰ))
      ∙ cong (subst B (sym w)) (sym (fromPathP (TmRecHomᴰ ρᴰ R)))
      ∙ subst⁻Subst B w R' )
      where
        sE : S
        sE = σeq .eqnSort e

        B : Yb sE → Type ℓXᴰ
        B = Xᴰ Nᴰ sE sᴰ

        fρ : (v : σeq .vars e) → Yb (σeq .varSort e v)
        fρ v = f (σeq .varSort e v) (ρ v)

        L' = TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ L
        R' = TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ R
        L'' = TmRecᴰ σᴰ Yb αN (Xᴰ Nᴰ) (Nᴰ .opsᴰ) {ρ = fρ} ρᴰ L

        u = TmRecHom ρ (σeq .lhs e)
        v = N .snd .snd e fρ
        w = TmRecHom ρ (σeq .rhs e)

        basefix : cong (f sE) (satM e ρ) ≡ u ∙ (v ∙ sym w)
        basefix = N .fst sE .snd _ _ _ _

  reindexMod : Modelᴰˢ σeq M σᴰ ℓXᴰ
  reindexMod .carrierᴰ s sᴰ x = Nᴰ .carrierᴰ s sᴰ (f s x)
  reindexMod .opsᴰ = ops*
  reindexMod .satᴰ = sat*

  private
    MODᴰᴰ' : Categoryᴰ (MOD σeq ℓX) _ _
    MODᴰᴰ' = MODᴰᴰ σeq {ℓX = ℓX} σᴰ {ℓXᴰ = ℓXᴰ}

  cartπ : MODᴰᴰ' [ hom ][ reindexMod , Nᴰ ]
  cartπ = (λ s sᴰ x xᴰ → xᴰ) , (λ o i x xᴰ y eq yᴰ hyp → hyp)

  cartβ : {L : Category.ob (MOD σeq ℓX)} {Lᴰ : Modelᴰˢ σeq L σᴰ ℓXᴰ}
    (g : ModHom σeq ℓX L M) (gᴰ : MODᴰᴰ' [ g ][ Lᴰ , reindexMod ])
    → Categoryᴰ._⋆ᴰ_ MODᴰᴰ' {f = g} {g = hom}
        {xᴰ = Lᴰ} {yᴰ = reindexMod} {zᴰ = Nᴰ} gᴰ cartπ
      ≡ gᴰ
  cartβ g gᴰ = refl

  -- Cartesianness: post-composition with `cartπ` is the IDENTITY
  -- function, and the two hom types it goes between are definitionally
  -- equal.  So `MODᴰᴰ` is a fibration, and every component of the
  -- universal property is `refl`.
  cartIso : {L : Category.ob (MOD σeq ℓX)} {Lᴰ : Modelᴰˢ σeq L σᴰ ℓXᴰ}
    (g : ModHom σeq ℓX L M)
    → Iso (MODᴰᴰ' [ g ][ Lᴰ , reindexMod ])
          (MODᴰᴰ' [ Category._⋆_ (MOD σeq ℓX) {x = L} {y = M} {z = N}
                      g hom ][ Lᴰ , Nᴰ ])
  cartIso {Lᴰ = Lᴰ} g .Iso.fun gᴰ =
    Categoryᴰ._⋆ᴰ_ MODᴰᴰ' {f = g} {g = hom}
      {xᴰ = Lᴰ} {yᴰ = reindexMod} {zᴰ = Nᴰ} gᴰ cartπ
  cartIso g .Iso.inv k = k
  cartIso g .Iso.sec _ = refl
  cartIso g .Iso.ret _ = refl
