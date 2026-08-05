-- Adjoining constants to a theory, in presheaf-valued models.
--
-- The presheaf counterpart of `Free.Constants`, whose theory
-- `σ[V] = σeq ⊕Eqns Pointed V` is reused verbatim.  Unfolding
-- `PshAlg σ[V] P` gives, at each `c`, an algebra together with a map
-- `V → P ⟅ c ⟆`, and `restr` being a homomorphism is exactly
-- naturality of that family.  So (`pshAlgConstIso`)
--
--     PshAlg σ[V] P  ≅  PshAlg σeq P × PshHomStrict (ΔPsh V) P
--
-- and the headline `isInitialFreePshOb[V]` follows: the free presheaf
-- model on the CONSTANT presheaf at `V` is the initial model of the
-- theory with `V`-many constants adjoined.
--
-- VERDICT ON VARYING CONSTANTS.  Constants indexed by a general
-- presheaf `Q` are NOT expressible in this framework.  `AlgTheorySig`'s
-- `ops` is a single `Type` and `PshAlg` interprets that one signature
-- in every fibre, so the constants of a theory always give a map out of
-- a CONSTANT presheaf -- there is no room for the op-set to vary over
-- `C`.  `initialRestrIsId`/`initialPshIsConstant` below turn this into
-- a mathematical, not merely syntactic, obstruction: the initial model
-- of ANY theory has constant underlying presheaf, whereas the would-be
-- initial "model with `Q`-many constants" is `FreePshOb σeq Q`, which
-- is not constant when `Q` is not.  The correct general statement is
-- coslice initiality (`isContrHomUnder`), which specialises to the
-- theory-extension statement exactly when `Q` is constant.
module Cubical.Algebra.Theory.Presheaf.Constants where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Unit using (tt)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Category
open import Cubical.Algebra.Theory.Constructions
open import Cubical.Algebra.Theory.Free.Constants
open import Cubical.Algebra.Theory.Free.Explicit
open import Cubical.Algebra.Theory.Free.Section
open import Cubical.Algebra.Theory.Presheaf.Base
open import Cubical.Algebra.Theory.Presheaf.Free
open import Cubical.Algebra.Theory.Presheaf.Unit

private
  variable
    ℓ ℓ' ℓ'' ℓv ℓX ℓC ℓC' : Level

open Functor
open PshAlg
open PshHomStrict

-- The constant presheaf on an arbitrary category.  Over the unit
-- category this is `Presheaf.Unit.ConstPsh`, on the nose.
ΔPsh : {C : Category ℓC ℓC'} → hSet ℓX → Presheaf C ℓX
ΔPsh X .F-ob _ = X
ΔPsh X .F-hom _ x = x
ΔPsh X .F-id = refl
ΔPsh X .F-seq _ _ = refl

-- The nullary selector, elaborated once: `⊥*` has no definitional eta,
-- so every use must be bridged by `funExt (λ ())` rather than `refl`.
noArgs : {A : Type ℓX} → ⊥* {ℓv} → A
noArgs ()

module _ {C : Category ℓC ℓC'} {σ : AlgTheorySig ℓ ℓ'}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) (P : Presheaf C ℓX) where
  private module P = PresheafNotation P

  -- `restr` is a family of propositions, so a presheaf model is
  -- determined by its fibrewise algebras.
  PshAlg≡ : {B D : PshAlg σeq P} → B .alg ≡ D .alg → B ≡ D
  PshAlg≡ p i .alg = p i
  PshAlg≡ {B = B} {D = D} p i .restr {c} {c'} f =
    isProp→PathP
      (λ j → isPropHomo σeq {B = p j c'} {C = p j c} {f = P._⋆_ f}
        (str (P ⟅ c ⟆)))
      (B .restr f) (D .restr f) i

-- THE UNFOLDING.  `σ[V] = σeq ⊕Eqns Pointed V` is the theory of
-- `Free.Constants`: `σeq` together with a nullary operation for each
-- `v : V` and no new equations.  In a presheaf model of `σ[V]` the
-- fibrewise algebra at `c` carries a map `V → P ⟅ c ⟆`, and `restr`
-- being a `σ[V]`-homomorphism says exactly that those maps commute
-- with restriction -- i.e. that they assemble into a strict presheaf
-- morphism out of the CONSTANT presheaf on `V`.
module _ {C : Category ℓC ℓC'} {σ : AlgTheorySig ℓ ℓv}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) (V : hSet ℓv) where

  private
    τ : AlgTheoryEqns (σ ⊕Sig PointedSig ⟨ V ⟩) (ℓ-max ℓ'' ℓ-zero) ℓv
    τ = σ[V] σeq ⟨ V ⟩

    ΔV : Presheaf C ℓv
    ΔV = ΔPsh V

  module _ (P : Presheaf C ℓX) where
    private module P = PresheafNotation P

    forgetPointsPsh : PshAlg τ P → PshAlg σeq P
    forgetPointsPsh B .alg c = forgetPoints σeq ⟨ V ⟩ (P ⟅ c ⟆) (B .alg c)
    forgetPointsPsh B .restr f .Homo.op-hom op x y eq =
      Homo.op-hom (B .restr f) (inl op) x y eq

    pointsPsh : PshAlg τ P → PshHomStrict ΔV P
    pointsPsh B .N-ob c = pointsAt σeq ⟨ V ⟩ (P ⟅ c ⟆) (B .alg c)
    pointsPsh B .N-hom c c' f v' v eq =
      Homo.op-hom (B .restr f) (inr v') noArgs
        (pointsAt σeq ⟨ V ⟩ (P ⟅ c' ⟆) (B .alg c') v')
        (cong (Alg.⟨_⟩⟦_⟧op (B .alg c') (inr v')) (funExt (λ ())))
      ∙ cong (Alg.⟨_⟩⟦_⟧op (B .alg c) (inr v')) (funExt (λ ()))
      ∙ cong (pointsAt σeq ⟨ V ⟩ (P ⟅ c ⟆) (B .alg c)) eq

    withPointsPsh : PshAlg σeq P → PshHomStrict ΔV P → PshAlg τ P
    withPointsPsh B α .alg c =
      withPoints σeq ⟨ V ⟩ (P ⟅ c ⟆) (B .alg c) (α .N-ob c)
    withPointsPsh B α .restr f .Homo.op-hom (inl op) x y eq =
      Homo.op-hom (B .restr f) op x y eq
    withPointsPsh B α .restr {c} {c'} f .Homo.op-hom (inr v) x y eq =
      cong (P._⋆_ f) eq ∙ α .N-hom c c' f v v refl

    -- DELIVERABLE 1.  A presheaf model of `σ[V]` is a presheaf model of
    -- `σeq` equipped with a map out of the constant presheaf on `V`.
    pshAlgConstIso :
      Iso (PshAlg τ P) (PshAlg σeq P × PshHomStrict ΔV P)
    pshAlgConstIso .Iso.fun B = forgetPointsPsh B , pointsPsh B
    pshAlgConstIso .Iso.inv (B , α) = withPointsPsh B α
    pshAlgConstIso .Iso.sec (B , α) =
      ΣPathP ( PshAlg≡ σeq P (funExt (λ c → AlgExt (str (P ⟅ c ⟆)) refl))
             , makePshHomStrictPath refl )
    pshAlgConstIso .Iso.ret B =
      PshAlg≡ τ P (funExt (λ c → AlgExt (str (P ⟅ c ⟆)) (funExt
        (λ { (inl op) → refl
           ; (inr v) → funExt (λ x →
               cong (Alg.⟨_⟩⟦_⟧op (B .alg c) (inr v))
                 (funExt (λ ()))) }))))

  -- THE FREE MODEL ON `V`.  Pointwise the free `σeq`-model on `V`, with
  -- the generators as the interpretations of the new constants.
  private
    ℓF = ℓFree ℓ ℓ'' ℓv

    FreeΔ : Category.ob (PMOD {C = C} σeq ℓF)
    FreeΔ = FreePshOb σeq ΔV

  FreePshOb[V] : Category.ob (PMOD {C = C} τ ℓF)
  FreePshOb[V] =
    FreeΔ .fst
    , withPointsPsh (FreeΔ .fst) (FreeΔ .snd) (genPsh σeq ΔV)

  private module Free[V] = PresheafNotation (FreePshOb[V] .fst)

  -- The free model on a CONSTANT presheaf has identity restrictions:
  -- `FreeF ⟪ id ⟫` is `rec var`, which is the identity by uniqueness.
  freeΔRestrIsId : {c c' : Category.ob C} (f : C [ c , c' ])
    (x : Free[V].p[ c' ]) → f Free[V].⋆ x ≡ x
  freeΔRestrIsId f x =
    sym (recUniq σeq trunc (FreeAlg σeq ⟨ V ⟩) _ (λ y → y) (idHomo σeq)
          (λ _ → refl) x)

  module _ (N : Category.ob (PMOD {C = C} τ ℓF)) where
    private
      Nσ : Category.ob (PMOD {C = C} σeq ℓF)
      Nσ = N .fst , forgetPointsPsh (N .fst) (N .snd)

      Nρ : PshHomStrict ΔV (N .fst)
      Nρ = pointsPsh (N .fst) (N .snd)

      ext : PModHom σeq ℓF FreeΔ Nσ
      ext = Iso.inv (UPPMod σeq ΔV Nσ) Nρ

      -- The extension preserves the new constants: `rec ρ (var v)` is
      -- `ρ v` on the nose.
      recHomo[V] : PshAlgHomo τ (ext .fst) (FreePshOb[V] .snd) (N .snd)
      recHomo[V] c .Homo.op-hom (inl op) x y eq =
        Homo.op-hom (ext .snd c) op x y eq
      recHomo[V] c .Homo.op-hom (inr v) x y eq =
        cong (ext .fst .N-ob c) eq
        ∙ cong (Alg.⟨_⟩⟦_⟧op (N .snd .alg c) (inr v)) (funExt (λ ()))

    module _ (α : PshHomStrict (FreePshOb[V] .fst) (N .fst))
      (ϕ : PshAlgHomo τ α (FreePshOb[V] .snd) (N .snd)) where
      private
        -- The `σeq`-part of an arbitrary `σ[V]`-homomorphism.
        ϕσ : PshAlgHomo σeq α (FreeΔ .snd) (Nσ .snd)
        ϕσ c .Homo.op-hom op x y eq = Homo.op-hom (ϕ c) (inl op) x y eq

        -- ... and its action on the new constants, which pins it down.
        genβPsh : ∀ c v → α .N-ob c (gen σeq ⟨ V ⟩ v) ≡ Nρ .N-ob c v
        genβPsh c v =
          Homo.op-hom (ϕ c) (inr v) noArgs (gen σeq ⟨ V ⟩ v) refl
          ∙ cong (Alg.⟨_⟩⟦_⟧op (N .snd .alg c) (inr v)) (funExt (λ ()))

      uniqExt : Path (PModHom σeq ℓF FreeΔ Nσ) (α , ϕσ) ext
      uniqExt =
        isoFunInjective (UPPMod σeq ΔV Nσ) _ _
          (makePshHomStrictPath (funExt (λ c → funExt (genβPsh c)))
           ∙ sym (Iso.sec (UPPMod σeq ΔV Nσ) Nρ))

    isContrPModHom[V] : isContr (PModHom τ ℓF FreePshOb[V] N)
    isContrPModHom[V] .fst = ext .fst , recHomo[V]
    isContrPModHom[V] .snd (α , ϕ) =
      Σ≡Prop (λ _ → isPropΠ (λ c → isPropHomo τ (str (N .fst ⟅ c ⟆))))
        (sym (cong fst (uniqExt α ϕ)))

  -- DELIVERABLE 2.  The free presheaf model on `V` is the INITIAL model
  -- of the theory extended by `V`-many constants.
  isInitialFreePshOb[V] : isInitial (PMOD {C = C} τ ℓF) FreePshOb[V]
  isInitialFreePshOb[V] = isContrPModHom[V]

  InitialPMOD[V] : Initial (PMOD {C = C} τ ℓF)
  InitialPMOD[V] = FreePshOb[V] , isInitialFreePshOb[V]

-- DELIVERABLE 3, THE OBSTRUCTION.  Constants indexed by a VARYING
-- presheaf are not expressible as a theory extension.
--
-- A signature's `ops` is a single `Type`, and `PshAlg` interprets that
-- one signature in every fibre.  So a nullary operation `o` yields an
-- element `o c : P ⟅ c ⟆` for EVERY `c`, and `restr f` being a
-- homomorphism forces `f ⋆ o c' ≡ o c`: the constants of a theory are
-- always global and constant, which is exactly the content of
-- `pshAlgConstIso` above.  To adjoin `Q ⟅ c ⟆`-many constants at `c`
-- one would need the op-set itself to vary over `C` -- a presheaf of
-- signatures -- which `AlgTheorySig` cannot express.
--
-- The following makes the obstruction sharp rather than merely
-- syntactic.  The initial model of ANY theory has CONSTANT underlying
-- presheaf: its restriction maps are the identity.  The candidate
-- "initial model of `σeq` with `Q`-many constants" would have to be
-- `FreePshOb σeq Q`, whose value at `c` is the free model on `Q ⟅ c ⟆`
-- and which is therefore not constant for varying `Q`.  So no theory
-- has `Q`-many constants, for any `Q` that is not (isomorphic to) a
-- constant presheaf.
module _ {C : Category ℓC ℓC'} {υ : AlgTheorySig ℓ ℓv}
  (υeq : AlgTheoryEqns υ ℓ'' ℓv) where
  private
    ℓF = ℓFree ℓ ℓ'' ℓv

    Ini : Presheaf C ℓF
    Ini = FreePshOb υeq (EmptyPsh υeq) .fst

    module Ini = PresheafNotation Ini

  initialRestrIsId : {c c' : Category.ob C} (f : C [ c , c' ])
    (x : Ini.p[ c' ]) → f Ini.⋆ x ≡ x
  initialRestrIsId f x =
    sym (recUniq υeq trunc (FreeAlg υeq _) _ (λ y → y) (idHomo υeq)
          (λ ()) x)

  initialPshIsConstant :
    PshIsoStrict (ΔPsh {C = C} (FreeModel υeq (⊥* {ℓv}) , trunc)) Ini
  initialPshIsConstant .PshIsoStrict.trans .N-ob c x = x
  initialPshIsConstant .PshIsoStrict.trans .N-hom c c' f x' x eq =
    initialRestrIsId f x' ∙ eq
  initialPshIsConstant .PshIsoStrict.nIso c =
    (λ x → x) , (λ _ → refl) , (λ _ → refl)

-- DELIVERABLE 3, THE POSITIVE REPLACEMENT.  For a general presheaf `Q`
-- of generators, freeness is still initiality -- but in the COSLICE
-- under `Q`, not in a category of models of an extended theory.  For
-- `Q = ΔPsh V` this is `isInitialFreePshOb[V]` above; the point of that
-- theorem is precisely that for constant `Q` the coslice IS a category
-- of models.
module _ {C : Category ℓC ℓC'} {σ : AlgTheorySig ℓ ℓv}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) (Q : Presheaf C ℓv) where
  private
    ℓF = ℓFree ℓ ℓ'' ℓv

  ModUnder : Type _
  ModUnder =
    Σ[ N ∈ Category.ob (PMOD {C = C} σeq ℓF) ] PshHomStrict Q (N .fst)

  HomUnder : (M : ModUnder) → Type _
  HomUnder M =
    Σ[ ϕ ∈ PModHom σeq ℓF (FreePshOb σeq Q) (M .fst) ]
      (genPsh σeq Q ⋆PshHomStrict (ϕ .fst) ≡ M .snd)

  isContrHomUnder : (M : ModUnder) → isContr (HomUnder M)
  isContrHomUnder M =
    isoToIsEquiv (UPPMod σeq Q (M .fst)) .equiv-proof (M .snd)

-- DELIVERABLE 4.  Over the unit category the presheaf theorem IS the
-- SET theorem of `Free.Constants`: evaluating `FreePshOb[V]` at the
-- unique object gives `FreeOb[V]` on the nose, and initiality transfers
-- back along the fully faithful `ConstMod`.
module _ {σ : AlgTheorySig ℓ ℓv} (σeq : AlgTheoryEqns σ ℓ'' ℓv)
  (V : hSet ℓv) where
  private
    τ : AlgTheoryEqns (σ ⊕Sig PointedSig ⟨ V ⟩) (ℓ-max ℓ'' ℓ-zero) ℓv
    τ = σ[V] σeq ⟨ V ⟩

    ℓF = ℓFree ℓ ℓ'' ℓv

    Free𝟙 : Category.ob (PMOD {C = 𝟙} τ ℓF)
    Free𝟙 = FreePshOb[V] {C = 𝟙} σeq V

  -- The presheaf free model evaluates to the SET free model on the nose.
  Ev-FreePshOb[V] : Ev {C = 𝟙} τ tt ⟅ Free𝟙 ⟆ ≡ FreeOb[V] σeq ⟨ V ⟩
  Ev-FreePshOb[V] = refl

  private
    -- `Free𝟙` and the constant model on `FreeOb[V]` have the same
    -- underlying family of sets and the same fibrewise algebras; they
    -- differ only in their restriction maps, which agree by
    -- `freeΔRestrIsId`.  So they corepresent the same homs.
    reIso : (M : Category.ob (PMOD {C = 𝟙} τ ℓF))
      → Iso (PMOD {C = 𝟙} τ ℓF [ Free𝟙 , M ])
            (PMOD {C = 𝟙} τ ℓF [ ConstMod τ ⟅ FreeOb[V] σeq ⟨ V ⟩ ⟆ , M ])
    reIso M .Iso.fun ψ .fst .N-ob = ψ .fst .N-ob
    reIso M .Iso.fun ψ .fst .N-hom c c' f x' x eq =
      ψ .fst .N-hom c c' f x' x (freeΔRestrIsId {C = 𝟙} σeq V f x' ∙ eq)
    reIso M .Iso.fun ψ .snd = ψ .snd
    reIso M .Iso.inv ψ .fst .N-ob = ψ .fst .N-ob
    reIso M .Iso.inv ψ .fst .N-hom c c' f x' x eq =
      ψ .fst .N-hom c c' f x' x (sym (freeΔRestrIsId {C = 𝟙} σeq V f x') ∙ eq)
    reIso M .Iso.inv ψ .snd = ψ .snd
    reIso M .Iso.sec ψ =
      Σ≡Prop (λ _ → isPropΠ (λ c → isPropHomo τ (str (M .fst ⟅ c ⟆))))
        (makePshHomStrictPath refl)
    reIso M .Iso.ret ψ =
      Σ≡Prop (λ _ → isPropΠ (λ c → isPropHomo τ (str (M .fst ⟅ c ⟆))))
        (makePshHomStrictPath refl)

  -- `Free.Constants.isInitialFreeOb[V]`, re-derived from the presheaf
  -- theorem over the unit category.
  isInitialFreeOb[V]FromPsh : isInitial (MOD τ ℓF) (FreeOb[V] σeq ⟨ V ⟩)
  isInitialFreeOb[V]FromPsh N =
    isOfHLevelRetractFromIso 0
      (compIso (ConstModHomIso τ {M = FreeOb[V] σeq ⟨ V ⟩} {N = N})
        (invIso (reIso (ConstMod τ ⟅ N ⟆))))
      (isInitialFreePshOb[V] {C = 𝟙} σeq V (ConstMod τ ⟅ N ⟆))
