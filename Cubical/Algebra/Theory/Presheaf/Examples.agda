{-# OPTIONS --lossy-unification #-}
-- Worked examples of presheaf-valued models.
--
-- The point of this file is to make `PshAlg` concrete:
--
--   * a *presheaf of monoids* is unfolded into a presheaf `P` together
--     with a `MonoidStr` on each `P ⟅ c ⟆` whose restriction maps are
--     monoid homomorphisms (`PshMonoidIso`), and likewise for groups
--     (`PshGroupIso`) and commutative rings (`PshCommRingIso`);
--   * two generic families of models are built --- the constant one and
--     the "functions on a diagram of sets" one --- and instantiated at a
--     genuinely concrete base category, the poset `(ℕ , ≤)`;
--   * the inclusion of constants is exhibited as a `PModHom`.
module Cubical.Algebra.Theory.Presheaf.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Empty
open import Cubical.Data.Int using (ℤ ; isSetℤ)
open import Cubical.Data.Nat using (ℕ ; isSetℕ ; _+_)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-refl ; ≤-trans ; isProp≤)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (isPropIsGroupHom)
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Algebra.Monoid.Instances.Nat using (NatMonoid)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Constructions
open import Cubical.Algebra.Theory.Category using (MOD)
open import Cubical.Algebra.Theory.Presheaf.Base
open import Cubical.Algebra.Instances.Monoid
open import Cubical.Algebra.Instances.Group
  using (GroupEqns ; AlgGroupStr ; AlgIsoGroupStr ; HomoIsoIsGroupHom)
open import Cubical.Algebra.Instances.Ring
  using (CommRingEqns ; AlgCommRingStr ; CommRingStrAlg ; AlgIsoCommRingStr
        ; HomoIsoIsCommRingHom)

private
  variable
    ℓ ℓ' ℓ'' ℓv ℓX ℓY ℓC ℓC' ℓs ℓh : Level

open AlgTheorySig
open AlgTheoryEqns

-- Models of `MonEqns` are monoid structures.  (`Instances/Group.agda`
-- and `Instances/Ring.agda` already do this for their theories; the
-- monoid case was missing.)
module _ {X : Type ℓX} (isSetX : isSet X) where

  AlgMonoidStr : Alg MonEqns X → MonoidStr X
  AlgMonoidStr B .MonoidStr.ε = ε where open MonNotation B
  AlgMonoidStr B .MonoidStr._·_ = _·_ where open MonNotation B
  AlgMonoidStr B .MonoidStr.isMonoid =
    makeIsMonoid isSetX (λ x y z → sym (assoc x y z)) unitR unitL
    where open MonNotation B

  MonoidStrAlg : MonoidStr X → Alg MonEqns X
  MonoidStrAlg M .Alg.⟨_⟩⟦_⟧op εOp _ = M .MonoidStr.ε
  MonoidStrAlg M .Alg.⟨_⟩⟦_⟧op ·Op g = MonoidStr._·_ M (g true) (g false)
  MonoidStrAlg M .Alg.⟦_⟧eqn unitLE ρ = MonoidStr.·IdL M (ρ tt)
  MonoidStrAlg M .Alg.⟦_⟧eqn unitRE ρ = MonoidStr.·IdR M (ρ tt)
  MonoidStrAlg M .Alg.⟦_⟧eqn assocE ρ =
    sym (MonoidStr.·Assoc M (ρ t0) (ρ t1) (ρ t2))

  AlgIsoMonoidStr : Iso (Alg MonEqns X) (MonoidStr X)
  AlgIsoMonoidStr .Iso.fun = AlgMonoidStr
  AlgIsoMonoidStr .Iso.inv = MonoidStrAlg
  AlgIsoMonoidStr .Iso.sec M i .MonoidStr.ε = M .MonoidStr.ε
  AlgIsoMonoidStr .Iso.sec M i .MonoidStr._·_ = M .MonoidStr._·_
  AlgIsoMonoidStr .Iso.sec M i .MonoidStr.isMonoid =
    isPropIsMonoid _ _
      (AlgMonoidStr (MonoidStrAlg M) .MonoidStr.isMonoid)
      (M .MonoidStr.isMonoid) i
  AlgIsoMonoidStr .Iso.ret B =
    AlgExt isSetX (funExt λ
      { εOp → funExt λ g → cong B.⟨ εOp ⟩⟦_⟧op (funExt λ ())
      ; ·Op → funExt λ g → cong B.⟨ ·Op ⟩⟦_⟧op (sym (selη g)) })
    where module B = Alg B

-- `Cubical.Algebra.Monoid.Base` does not ship this one.
isPropIsMonoidHom' : {X : Type ℓX} {Y : Type ℓY} (isSetY : isSet Y)
  (M : MonoidStr X) (f : X → Y) (N : MonoidStr Y)
  → isProp (IsMonoidHom M f N)
isPropIsMonoidHom' isSetY M f N ϕ ψ i .IsMonoidHom.presε =
  isSetY _ _ (ϕ .IsMonoidHom.presε) (ψ .IsMonoidHom.presε) i
isPropIsMonoidHom' isSetY M f N ϕ ψ i .IsMonoidHom.pres· x y =
  isSetY _ _ (ϕ .IsMonoidHom.pres· x y) (ψ .IsMonoidHom.pres· x y) i

-- Homomorphisms of models are monoid homomorphisms.
module _ {X : Type ℓX} {Y : Type ℓY} (isSetX : isSet X) (isSetY : isSet Y)
  (B : Alg MonEqns X) (C : Alg MonEqns Y) {f : X → Y} where

  private
    module B = Alg B
    module C = Alg C

  HomoIsMonoidHom : Homo MonEqns f B C
    → IsMonoidHom (AlgMonoidStr isSetX B) f (AlgMonoidStr isSetY C)
  HomoIsMonoidHom ϕ .IsMonoidHom.presε =
    Homo.op-hom' ϕ εOp _ ∙ cong C.⟨ εOp ⟩⟦_⟧op (funExt λ ())
  HomoIsMonoidHom ϕ .IsMonoidHom.pres· x y =
    Homo.op-hom' ϕ ·Op (sel x y)
    ∙ cong C.⟨ ·Op ⟩⟦_⟧op (funExt λ { true → refl ; false → refl })

  IsMonoidHomHomo
    : IsMonoidHom (AlgMonoidStr isSetX B) f (AlgMonoidStr isSetY C)
    → Homo MonEqns f B C
  IsMonoidHomHomo ψ .Homo.op-hom εOp x y eq =
    cong f eq
    ∙ cong f (cong B.⟨ εOp ⟩⟦_⟧op (funExt λ ()))
    ∙ ψ .IsMonoidHom.presε
    ∙ cong C.⟨ εOp ⟩⟦_⟧op (funExt λ ())
  IsMonoidHomHomo ψ .Homo.op-hom ·Op x y eq =
    cong f eq
    ∙ cong f (cong B.⟨ ·Op ⟩⟦_⟧op (selη x))
    ∙ ψ .IsMonoidHom.pres· (x true) (x false)
    ∙ cong C.⟨ ·Op ⟩⟦_⟧op (sym (selη _))

  HomoIsoIsMonoidHom : Iso (Homo MonEqns f B C)
    (IsMonoidHom (AlgMonoidStr isSetX B) f (AlgMonoidStr isSetY C))
  HomoIsoIsMonoidHom .Iso.fun = HomoIsMonoidHom
  HomoIsoIsMonoidHom .Iso.inv = IsMonoidHomHomo
  HomoIsoIsMonoidHom .Iso.sec ψ = isPropIsMonoidHom' isSetY _ _ _ _ ψ
  HomoIsoIsMonoidHom .Iso.ret ϕ = isPropHomo MonEqns isSetY _ ϕ

-- Unfolding a presheaf model, once and for all.
--
-- Given a theory whose models are a familiar structure (`Str`) and
-- whose homomorphisms are the familiar homomorphisms (`IsHom`), a
-- presheaf model of that theory is exactly a fibrewise `Str` whose
-- restriction maps are `IsHom`s.  Nothing about presheaves is used
-- beyond `PshAlgIsoΣ`; the content is the Σ-shuffle.
module Unfolding {C : Category ℓC ℓC'} {σ : AlgTheorySig ℓ ℓ'}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv)
  (Str : hSet ℓX → Type ℓs)
  (IsHom : {X Y : hSet ℓX} → Str X → (⟨ X ⟩ → ⟨ Y ⟩) → Str Y → Type ℓh)
  (isPropIsHom : {X Y : hSet ℓX} (M : Str X) (f : ⟨ X ⟩ → ⟨ Y ⟩) (N : Str Y)
    → isProp (IsHom M f N))
  (algIso : (X : hSet ℓX) → Iso (Alg σeq ⟨ X ⟩) (Str X))
  (homIso : {X Y : hSet ℓX} (B : Alg σeq ⟨ X ⟩) (D : Alg σeq ⟨ Y ⟩)
    (f : ⟨ X ⟩ → ⟨ Y ⟩)
    → Iso (Homo σeq f B D)
        (IsHom (algIso X .Iso.fun B) f (algIso Y .Iso.fun D)))
  where

  private
    module C = Category C
  open PshAlg

  module _ (P : Presheaf C ℓX) where
    private module P = PresheafNotation P

    -- fibrewise structures
    PshStrOb : Type _
    PshStrOb = ∀ (c : C.ob) → Str (P ⟅ c ⟆)

    -- ... whose restriction maps are homomorphisms
    PshStrRestr : PshStrOb → Type _
    PshStrRestr M =
      ∀ {c c'} (f : C [ c , c' ]) → IsHom (M c') (P._⋆_ f) (M c)

    PshStr : Type _
    PshStr = Σ PshStrOb PshStrRestr

    private
      isPropPshStrRestr : ∀ M → isProp (PshStrRestr M)
      isPropPshStrRestr M =
        isPropImplicitΠ2 λ _ _ → isPropΠ λ _ → isPropIsHom _ _ _

      isPropAlgRestr : (A : ∀ (c : C.ob) → Alg σeq P.p[ c ])
        → isProp (∀ {c c'} (f : C [ c , c' ])
                    → Homo σeq (P._⋆_ f) (A c') (A c))
      isPropAlgRestr A =
        isPropImplicitΠ2 λ c _ → isPropΠ λ _ →
          isPropHomo σeq (str (P ⟅ c ⟆))

    PshAlgIsoStr : Iso (PshAlg σeq P) PshStr
    PshAlgIsoStr .Iso.fun B =
      (λ c → algIso (P ⟅ c ⟆) .Iso.fun (B .alg c))
      , λ f → homIso _ _ _ .Iso.fun (B .restr f)
    PshAlgIsoStr .Iso.inv (M , k) .alg c = algIso (P ⟅ c ⟆) .Iso.inv (M c)
    PshAlgIsoStr .Iso.inv (M , k) .restr {c} {c'} f =
      homIso _ _ _ .Iso.inv
        (subst2 (λ m n → IsHom m (P._⋆_ f) n)
          (sym (algIso (P ⟅ c' ⟆) .Iso.sec (M c')))
          (sym (algIso (P ⟅ c ⟆) .Iso.sec (M c)))
          (k f))
    PshAlgIsoStr .Iso.sec (M , k) =
      Σ≡Prop isPropPshStrRestr
        (funExt λ c → algIso (P ⟅ c ⟆) .Iso.sec (M c))
    PshAlgIsoStr .Iso.ret B =
      isoFunInjective (PshAlgIsoΣ σeq P) _ _
        (Σ≡Prop isPropAlgRestr
          (funExt λ c → algIso (P ⟅ c ⟆) .Iso.ret (B .alg c)))

-- (1) Presheaves of monoids.
--
-- `PshMonoidStr P` is, by definition, a `MonoidStr` on every `P ⟅ c ⟆`
-- together with the statement that every restriction map `f ⋆_` is a
-- monoid homomorphism; `PshMonoidIso` says that this is exactly a
-- `PshAlg MonEqns P`.
PSHMONOID : (C : Category ℓC ℓC') (ℓX : Level) → Category _ _
PSHMONOID C ℓX = PMOD {C = C} MonEqns ℓX

module _ {C : Category ℓC ℓC'} {ℓX : Level} where
  open Unfolding {C = C} MonEqns
    (λ (X : hSet ℓX) → MonoidStr ⟨ X ⟩)
    (λ M f N → IsMonoidHom M f N)
    (λ {_} {Y} M f N → isPropIsMonoidHom' (str Y) M f N)
    (λ X → AlgIsoMonoidStr (str X))
    (λ {X} {Y} B D f → HomoIsoIsMonoidHom (str X) (str Y) B D)
    using ()
    renaming (PshStr to PshMonoidStr ; PshAlgIsoStr to PshMonoidIso)
    public

-- (2) Presheaves of groups and of commutative rings.  Nothing is
-- re-derived: `Instances/Group.agda` and `Instances/Ring.agda` already
-- identify models with structures and homomorphisms with
-- homomorphisms, so `Unfolding` applies verbatim.
--
-- `PshCommRingStr P` is the algebraic core of a ringed space: a
-- commutative ring on every `P ⟅ c ⟆` with ring-homomorphic
-- restrictions, and no sheaf condition anywhere.
PSHGROUP : (C : Category ℓC ℓC') (ℓ : Level) → Category _ _
PSHGROUP C ℓ = PMOD {C = C} (GroupEqns ℓ) ℓ

PSHCOMMRING : (C : Category ℓC ℓC') (ℓ : Level) → Category _ _
PSHCOMMRING C ℓ = PMOD {C = C} (CommRingEqns ℓ) ℓ

module _ {C : Category ℓC ℓC'} {ℓ : Level} where
  open Unfolding {C = C} (GroupEqns ℓ)
    (λ (X : hSet ℓ) → GroupStr ⟨ X ⟩)
    (λ M f N → IsGroupHom M f N)
    (λ {X} {Y} M f N → isPropIsGroupHom (⟨ X ⟩ , M) (⟨ Y ⟩ , N))
    (λ X → AlgIsoGroupStr (str X))
    (λ {X} {Y} B D f → HomoIsoIsGroupHom (str X) (str Y) B D)
    using ()
    renaming (PshStr to PshGroupStr ; PshAlgIsoStr to PshGroupIso)
    public

  open Unfolding {C = C} (CommRingEqns ℓ)
    (λ (X : hSet ℓ) → CommRingStr ⟨ X ⟩)
    (λ M f N → IsCommRingHom M f N)
    (λ M f N → isPropIsCommRingHom M f N)
    (λ X → AlgIsoCommRingStr (str X))
    (λ {X} {Y} B D f → HomoIsoIsCommRingHom (str X) (str Y) B D)
    using ()
    renaming (PshStr to PshCommRingStr ; PshAlgIsoStr to PshCommRingIso)
    public

-- Two generic families of presheaf models, for an arbitrary theory.
module _ {C : Category ℓC ℓC'} {σ : AlgTheorySig ℓ ℓ'}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) {X : hSet ℓX} (B : Alg σeq ⟨ X ⟩) where

  private module C = Category C
  open Functor
  open PshAlg
  open PshHomStrict

  -- The constant presheaf, with identity restriction maps.  (This is
  -- `ConstPsh` from `Presheaf/Unit.agda`, over an arbitrary base.)
  ΔPsh : Presheaf C ℓX
  ΔPsh .F-ob _ = X
  ΔPsh .F-hom _ x = x
  ΔPsh .F-id = refl
  ΔPsh .F-seq _ _ = refl

  ΔPshAlg : PshAlg σeq ΔPsh
  ΔPshAlg .alg _ = B
  ΔPshAlg .restr _ = idHomo σeq

  ΔModel : Category.ob (PMOD {C = C} σeq ℓX)
  ΔModel = ΔPsh , ΔPshAlg

  -- `X`-valued functions on a diagram of sets, with pointwise
  -- operations and restriction by precomposition.  Since `S` is
  -- covariant, precomposition is contravariant, so this is a presheaf.
  module _ (S : Functor C (SET ℓX)) where

    FunPsh : Presheaf C ℓX
    FunPsh .F-ob c = (⟨ S ⟅ c ⟆ ⟩ → ⟨ X ⟩) , isSet→ (str X)
    FunPsh .F-hom f φ = φ ∘ S ⟪ f ⟫
    FunPsh .F-id = funExt λ φ → cong (φ ∘_) (S .F-id)
    FunPsh .F-seq f g = funExt λ φ → cong (φ ∘_) (S .F-seq g f)

    -- Pointwise operations: the fibres are powers of `B`, and
    -- precomposition is a homomorphism on the nose.
    FunPshAlg : PshAlg σeq FunPsh
    FunPshAlg .alg c = powerAlg σeq B
    FunPshAlg .restr f .Homo.op-hom op x y eq = cong (_∘ S ⟪ f ⟫) eq

    FunModel : Category.ob (PMOD {C = C} σeq ℓX)
    FunModel = FunPsh , FunPshAlg

    -- (4) The inclusion of constants, as a homomorphism of presheaf
    -- models.
    constantsPsh : PshHomStrict ΔPsh FunPsh
    constantsPsh .N-ob c x _ = x
    constantsPsh .N-hom c c' f x' x eq = cong (λ z _ → z) eq

    constantsAlgHomo : PshAlgHomo σeq constantsPsh ΔPshAlg FunPshAlg
    constantsAlgHomo c .Homo.op-hom op x y eq = cong (λ z _ → z) eq

    constants : PModHom σeq ℓX ΔModel FunModel
    constants = constantsPsh , constantsAlgHomo

-- (3) A genuinely concrete instance.
--
-- Base category: the poset (ℕ , ≤).  Diagram of sets: the downset
-- functor `n ↦ ↓n = {k | k ≤ n}`, covariant because `m ≤ n` includes
-- `↓m` into `↓n`.  `FunPsh` then produces the presheaf of `X`-valued
-- functions on downsets, restricted along those inclusions.
ℕ≤ : Category ℓ-zero ℓ-zero
ℕ≤ .Category.ob = ℕ
ℕ≤ .Category.Hom[_,_] m n = m ≤ n
ℕ≤ .Category.id = ≤-refl
ℕ≤ .Category._⋆_ = ≤-trans
ℕ≤ .Category.⋆IdL _ = isProp≤ _ _
ℕ≤ .Category.⋆IdR _ = isProp≤ _ _
ℕ≤ .Category.⋆Assoc _ _ _ = isProp≤ _ _
ℕ≤ .Category.isSetHom = isProp→isSet isProp≤

Downset : Functor ℕ≤ (SET ℓ-zero)
Downset .Functor.F-ob n =
  (Σ[ k ∈ ℕ ] k ≤ n) , isSetΣ isSetℕ λ _ → isProp→isSet isProp≤
Downset .Functor.F-hom m≤n (k , k≤m) = k , ≤-trans k≤m m≤n
Downset .Functor.F-id = funExt λ _ → ΣPathP (refl , isProp≤ _ _)
Downset .Functor.F-seq _ _ = funExt λ _ → ΣPathP (refl , isProp≤ _ _)

ℕSet : hSet ℓ-zero
ℕSet = ℕ , isSetℕ

ℤSet : hSet ℓ-zero
ℤSet = ℤ , isSetℤ

ℕAlg : Alg MonEqns ℕ
ℕAlg = MonoidStrAlg isSetℕ (NatMonoid .snd)

ℤAlg : Alg (CommRingEqns ℓ-zero) ℤ
ℤAlg = CommRingStrAlg isSetℤ (ℤCommRing .snd)

-- A presheaf of monoids on (ℕ , ≤): `n ↦ (↓n → ℕ)` under pointwise
-- addition, restricted along the inclusions of downsets.
ℕFunModel : Category.ob (PSHMONOID ℕ≤ ℓ-zero)
ℕFunModel = FunModel MonEqns {X = ℕSet} ℕAlg Downset

ℕFunMonoidStr : PshMonoidStr (ℕFunModel .fst)
ℕFunMonoidStr = PshMonoidIso (ℕFunModel .fst) .Iso.fun (ℕFunModel .snd)

-- The fibrewise monoid really is the pointwise one.
_ : ∀ n → ℕFunMonoidStr .fst n .MonoidStr.ε ≡ (λ _ → 0)
_ = λ n → refl

_ : ∀ n (φ ψ : (Σ[ k ∈ ℕ ] k ≤ n) → ℕ)
  → MonoidStr._·_ (ℕFunMonoidStr .fst n) φ ψ ≡ (λ k → φ k + ψ k)
_ = λ n φ ψ → refl

-- ... and restriction along `m ≤ n` really is precomposition.
_ : ∀ {m n} (m≤n : m ≤ n) (φ : (Σ[ k ∈ ℕ ] k ≤ n) → ℕ)
  → PresheafNotation._⋆_ (ℕFunModel .fst) m≤n φ
    ≡ (λ (k , k≤m) → φ (k , ≤-trans k≤m m≤n))
_ = λ m≤n φ → refl

-- The same construction with ℤ gives a presheaf of commutative rings:
-- the algebraic core of a structure sheaf, with no sheaf condition.
ℤFunModel : Category.ob (PSHCOMMRING ℕ≤ ℓ-zero)
ℤFunModel = FunModel (CommRingEqns ℓ-zero) {X = ℤSet} ℤAlg Downset

ℤFunCommRingStr : PshCommRingStr (ℤFunModel .fst)
ℤFunCommRingStr = PshCommRingIso (ℤFunModel .fst) .Iso.fun (ℤFunModel .snd)

-- (4) A concrete homomorphism of presheaf models: the constants.
ℕConstantsHom
  : PModHom MonEqns ℓ-zero (ΔModel MonEqns {X = ℕSet} ℕAlg) ℕFunModel
ℕConstantsHom = constants MonEqns {X = ℕSet} ℕAlg Downset

ℤConstantsHom : PModHom (CommRingEqns ℓ-zero) ℓ-zero
  (ΔModel (CommRingEqns ℓ-zero) {X = ℤSet} ℤAlg) ℤFunModel
ℤConstantsHom = constants (CommRingEqns ℓ-zero) {X = ℤSet} ℤAlg Downset

-- `Presheaf/Base.agda` already gives evaluation at an object as a
-- functor `PMOD C σeq ℓX → MOD σeq ℓX`; here it is at work, extracting
-- the monoid of ℕ-valued functions on the downset of 2.
ℕFunAt2 : Category.ob (MOD MonEqns ℓ-zero)
ℕFunAt2 = Ev {C = ℕ≤} MonEqns 2 .Functor.F-ob ℕFunModel

_ : ℕFunAt2 .fst ≡ (((Σ[ k ∈ ℕ ] k ≤ 2) → ℕ) , isSet→ isSetℕ)
_ = refl
