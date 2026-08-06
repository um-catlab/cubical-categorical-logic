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
-- The fibration structure that used to sit at the end of this file --
-- `reindexMod` and its cartesian lift -- is now
-- `Cubical.Algebra.Theory.Sorted.Displayed.Reindex`.
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

