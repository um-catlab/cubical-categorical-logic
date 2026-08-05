-- Polynomial rings.
--
-- A polynomial ring is the free commutative ring on its variables, and
-- its universal property is evaluation: a ring homomorphism out of
-- ℤ[V] is exactly an assignment of a value to each variable.  Making
-- the variables *constants* -- the `Pointed V` summand -- turns that
-- into initiality: ℤ[V] is the initial commutative ring equipped with
-- V-many chosen elements.
--
-- Nothing here is specific to the polynomials: every statement is an
-- instantiation of the generic free-model machinery at `CommRingEqns`.
module Cubical.Algebra.Instances.PolynomialRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inr)
open import Cubical.Data.Unit using (Unit; tt)

open import Cubical.Algebra.CommRing.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Initial

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Category
open import Cubical.Algebra.Theory.Constructions using (_⊕Sig_)
open import Cubical.Algebra.Theory.Free.Explicit
  using (FreeModel; FreeAlg; trunc)
open import Cubical.Algebra.Theory.Presentation
  using (Presentation; PresEqns'; RelEqns; Alg∪; TmRec-closeTm)
open import Cubical.Algebra.Theory.Free.Section
open import Cubical.Algebra.Theory.Free.Constants
open import Cubical.Algebra.Instances.Ring

private
  variable
    ℓ : Level

-- ℤ[V], the polynomial ring on the variable set V.
module _ {ℓ : Level} (V : Type ℓ) where

  Poly : Type (ℓ-suc ℓ)
  Poly = FreeModel (CommRingEqns ℓ) V

  isSetPoly : isSet Poly
  isSetPoly = trunc

  PolyAlg : Alg (CommRingEqns ℓ) Poly
  PolyAlg = FreeAlg (CommRingEqns ℓ) V

  open CommRingNotation PolyAlg

  -- ℤ[V] as an honest `CommRingStr`, so it connects to the standard
  -- library.  This is `AlgCommRingStr` of `Instances/Ring.agda`, whose
  -- statement pins the carrier to the *theory's* level; the free model
  -- on a `Type ℓ` sits at `ℓ-suc ℓ`, so only the level-polymorphic
  -- half -- `CommRingNotation`, the laws themselves -- applies here.
  PolyCommRingStr : CommRingStr Poly
  PolyCommRingStr .CommRingStr.0r = 0r
  PolyCommRingStr .CommRingStr.1r = 1r
  PolyCommRingStr .CommRingStr._+_ = _+_
  PolyCommRingStr .CommRingStr._·_ = _·_
  PolyCommRingStr .CommRingStr.-_ = -_
  PolyCommRingStr .CommRingStr.isCommRing =
    makeIsCommRing isSetPoly +Assoc +IdR +InvR +Comm ·Assoc ·IdR
      ·DistR+ ·Comm

  PolyCommRing : CommRing (ℓ-suc ℓ)
  PolyCommRing = Poly , PolyCommRingStr

  -- ℤ[V] as an object of the category of commutative rings
  PolyOb : Category.ob (MOD (CommRingEqns ℓ) (ℓ-suc ℓ))
  PolyOb = FreeOb (CommRingEqns ℓ) V

  -- the variables, as polynomials
  polyVar : V → Poly
  polyVar = gen (CommRingEqns ℓ) V

  -- The universal property, stated as evaluation: a commutative ring
  -- homomorphism out of ℤ[V] is EXACTLY an assignment of a value to
  -- each variable.
  module _ (N : Category.ob (MOD (CommRingEqns ℓ) (ℓ-suc ℓ))) where
    private
      PolyHom : Type (ℓ-suc ℓ)
      PolyHom = ModHom (CommRingEqns ℓ) (ℓ-suc ℓ) PolyOb N

    evalUP : Iso PolyHom (V → ⟨ N .fst ⟩)
    evalUP = UPMod (CommRingEqns ℓ) V N

    eval : (V → ⟨ N .fst ⟩) → PolyHom
    eval = Iso.inv evalUP

    assignment : PolyHom → V → ⟨ N .fst ⟩
    assignment = Iso.fun evalUP

    -- β: evaluating at a variable gives back the assigned value
    evalβ : (ρ : V → ⟨ N .fst ⟩) (v : V) → eval ρ .fst (polyVar v) ≡ ρ v
    evalβ ρ v = refl

    -- η: every homomorphism is evaluation at its own assignment
    evalη : (f : PolyHom) → eval (assignment f) ≡ f
    evalη = Iso.ret evalUP

  -- Initiality.  `CommRing[V]` is the theory of a commutative ring
  -- together with a chosen element for each variable: the coproduct of
  -- the theory of commutative rings with `V`-many constants.
  CommRing[V] : AlgTheoryEqns (RingSig ℓ ⊕Sig PointedSig V) ℓ ℓ
  CommRing[V] = σ[V] (CommRingEqns ℓ) V

  PolyOb[V] : Category.ob (MOD CommRing[V] (ℓ-suc ℓ))
  PolyOb[V] = FreeOb[V] (CommRingEqns ℓ) V

  -- THE THEOREM: ℤ[V] is the initial commutative ring equipped with
  -- V-many chosen elements.
  isInitialPoly : isInitial (MOD CommRing[V] (ℓ-suc ℓ)) PolyOb[V]
  isInitialPoly = isInitialFreeOb[V] (CommRingEqns ℓ) V

  InitialPoly : Initial (MOD CommRing[V] (ℓ-suc ℓ))
  InitialPoly = InitialMOD[V] (CommRingEqns ℓ) V

  -- Unfolded: for any commutative ring `(X , B)` and any choice `ρ` of
  -- V-many of its elements there is a unique homomorphism ℤ[V] → X
  -- respecting that choice, and it sends each variable to its value.
  module _ (X : hSet (ℓ-suc ℓ)) (B : Alg (CommRingEqns ℓ) ⟨ X ⟩)
    (ρ : V → ⟨ X ⟩) where

    RingWithPoints : Category.ob (MOD CommRing[V] (ℓ-suc ℓ))
    RingWithPoints = X , withPoints (CommRingEqns ℓ) V X B ρ

    evalAt : ModHom CommRing[V] (ℓ-suc ℓ) PolyOb[V] RingWithPoints
    evalAt = isInitialPoly RingWithPoints .fst

    evalAtβ : (v : V) → evalAt .fst (polyVar v) ≡ ρ v
    evalAtβ v = refl

    evalAtUniq
      : (f : ModHom CommRing[V] (ℓ-suc ℓ) PolyOb[V] RingWithPoints)
      → evalAt ≡ f
    evalAtUniq = isInitialPoly RingWithPoints .snd

-- No variables: ℤ[∅] is the initial commutative ring.
isInitialPoly⊥
  : isInitial (MOD (CommRingEqns ℓ) (ℓ-suc ℓ)) (PolyOb (⊥* {ℓ}))
isInitialPoly⊥ = isInitialFreeOb (CommRingEqns _)

InitialCommRing : Initial (MOD (CommRingEqns ℓ) (ℓ-suc ℓ))
InitialCommRing = InitialMOD (CommRingEqns _)

-- ℤ[x], one variable.  Its universal property is that a homomorphism
-- out of it is a single element of the target.
module OneVariable where
  ℤ[x] : Type₁
  ℤ[x] = Poly Unit

  x : ℤ[x]
  x = polyVar Unit tt

  ℤ[x]Ob : Category.ob (MOD (CommRingEqns ℓ-zero) (ℓ-suc ℓ-zero))
  ℤ[x]Ob = PolyOb Unit

  module _ (N : Category.ob (MOD (CommRingEqns ℓ-zero) (ℓ-suc ℓ-zero)))
    where
    private
      unitIso : Iso (Unit → ⟨ N .fst ⟩) ⟨ N .fst ⟩
      unitIso .Iso.fun ρ = ρ tt
      unitIso .Iso.inv a _ = a
      unitIso .Iso.sec a = refl
      unitIso .Iso.ret ρ = refl

    evalOneUP
      : Iso (ModHom (CommRingEqns ℓ-zero) (ℓ-suc ℓ-zero) ℤ[x]Ob N)
            ⟨ N .fst ⟩
    evalOneUP = compIso (evalUP Unit N) unitIso

    evalOneβ : (a : ⟨ N .fst ⟩) → Iso.inv evalOneUP a .fst x ≡ a
    evalOneβ a = refl

-- ℤ[x,y], two variables: a homomorphism out of it is a pair.
module TwoVariables where
  ℤ[x,y] : Type₁
  ℤ[x,y] = Poly Bool

  x y : ℤ[x,y]
  x = polyVar Bool true
  y = polyVar Bool false

  ℤ[x,y]Ob : Category.ob (MOD (CommRingEqns ℓ-zero) (ℓ-suc ℓ-zero))
  ℤ[x,y]Ob = PolyOb Bool

  module _ (N : Category.ob (MOD (CommRingEqns ℓ-zero) (ℓ-suc ℓ-zero)))
    where
    private
      pair : ⟨ N .fst ⟩ → ⟨ N .fst ⟩ → Bool → ⟨ N .fst ⟩
      pair a b true = a
      pair a b false = b

      boolIso : Iso (Bool → ⟨ N .fst ⟩) (⟨ N .fst ⟩ × ⟨ N .fst ⟩)
      boolIso .Iso.fun ρ = ρ true , ρ false
      boolIso .Iso.inv (a , b) = pair a b
      boolIso .Iso.sec (a , b) = refl
      boolIso .Iso.ret ρ = funExt (λ { true → refl ; false → refl })

    evalTwoUP
      : Iso (ModHom (CommRingEqns ℓ-zero) (ℓ-suc ℓ-zero) ℤ[x,y]Ob N)
            (⟨ N .fst ⟩ × ⟨ N .fst ⟩)
    evalTwoUP = compIso (evalUP Bool N) boolIso

    evalTwoβ : (ab : ⟨ N .fst ⟩ × ⟨ N .fst ⟩)
      → (Iso.inv evalTwoUP ab .fst x ≡ ab .fst)
      × (Iso.inv evalTwoUP ab .fst y ≡ ab .snd)
    evalTwoβ ab = refl , refl

-- Polynomials over a base commutative ring R.
--
-- The theory of commutative R-algebras is the theory of commutative
-- rings with a constant for each element of R, subject to R's own
-- operation table as relations -- a model is a commutative ring with
-- an R-indexed family of elements preserving R's operations, i.e. a
-- ring homomorphism out of R -- and that is what `pres+` .. `pres1`
-- below say.  `R[V]` is then the free model of that theory on V.
--
-- What is NOT proved here: that the coefficient map R → R[V] is an
-- embedding, or that R[V] agrees with any other construction of the
-- polynomial ring over R.  Only the universal property is available.
module _ (R : CommRing ℓ) where
  private
    module R = CommRingStr (R .snd)

  open Presentation

  data TableRel : Type ℓ where
    +tab ·tab : ⟨ R ⟩ → ⟨ R ⟩ → TableRel
    -tab : ⟨ R ⟩ → TableRel
    0tab 1tab : TableRel

  -- R's operation table, as relations between the constants
  Table : Presentation (RingSig ℓ) ⟨ R ⟩ ℓ
  Table .rels = TableRel
  Table .rl (+tab a b) = tm+ (var a) (var b)
  Table .rr (+tab a b) = var (R._+_ a b)
  Table .rl (·tab a b) = tm· (var a) (var b)
  Table .rr (·tab a b) = var (R._·_ a b)
  Table .rl (-tab a) = tm- (var a)
  Table .rr (-tab a) = var (R.-_ a)
  Table .rl 0tab = tm0
  Table .rr 0tab = var R.0r
  Table .rl 1tab = tm1
  Table .rr 1tab = var R.1r

  -- the theory of commutative R-algebras
  CommAlgebra[R] : AlgTheoryEqns (RingSig ℓ ⊕Sig PointedSig ⟨ R ⟩) ℓ ℓ
  CommAlgebra[R] = PresEqns' Table (CommRingEqns ℓ)

  module _ (V : Type ℓ) where
    R[V] : Type (ℓ-suc ℓ)
    R[V] = FreeModel CommAlgebra[R] V

    R[V]Alg : Alg CommAlgebra[R] R[V]
    R[V]Alg = FreeAlg CommAlgebra[R] V

    -- the coefficients, as polynomials
    coeff : ⟨ R ⟩ → R[V]
    coeff a = Alg.⟨_⟩⟦_⟧op R[V]Alg (inr a) (λ ())

    -- the variables, as polynomials
    varR : V → R[V]
    varR = gen CommAlgebra[R] V

    R[V]Ob : Category.ob (MOD (σ[V] CommAlgebra[R] V) (ℓ-suc ℓ))
    R[V]Ob = FreeOb[V] CommAlgebra[R] V

    -- R[V] is the initial commutative R-algebra equipped with V-many
    -- chosen elements
    isInitialR[V]
      : isInitial (MOD (σ[V] CommAlgebra[R] V) (ℓ-suc ℓ)) R[V]Ob
    isInitialR[V] = isInitialFreeOb[V] CommAlgebra[R] V

    InitialR[V] : Initial (MOD (σ[V] CommAlgebra[R] V) (ℓ-suc ℓ))
    InitialR[V] = InitialMOD[V] CommAlgebra[R] V

  -- Every model of `CommAlgebra[R]` really is a commutative R-algebra:
  -- its constants preserve R's operations, i.e. they assemble into a
  -- ring homomorphism out of R.
  module _ {ℓX : Level} (X : hSet ℓX) (N : Alg CommAlgebra[R] ⟨ X ⟩) where
    private
      α = Alg.⟨_⟩⟦_⟧op N

    -- the underlying commutative ring, forgetting the constants
    baseAlg : Alg (CommRingEqns ℓ) ⟨ X ⟩
    baseAlg = forgetPoints (CommRingEqns ℓ) ⟨ R ⟩ X
      (Alg∪ (σ[V] (CommRingEqns ℓ) ⟨ R ⟩) (RelEqns Table) N)

    open CommRingNotation baseAlg

    -- the structure map R → X
    strMap : ⟨ R ⟩ → ⟨ X ⟩
    strMap a = α (inr a) (λ ())

    pres+ : (a b : ⟨ R ⟩) → strMap (R._+_ a b) ≡ strMap a + strMap b
    pres+ a b = sym
      ( sym (+Tm strMap (var a) (var b))
      ∙ sym (TmRec-closeTm α (λ ()) (Table .rl (+tab a b)))
      ∙ Alg.⟦_⟧eqn N (inr (+tab a b)) (λ ())
      ∙ TmRec-closeTm α (λ ()) (Table .rr (+tab a b)) )

    pres· : (a b : ⟨ R ⟩) → strMap (R._·_ a b) ≡ strMap a · strMap b
    pres· a b = sym
      ( sym (·Tm strMap (var a) (var b))
      ∙ sym (TmRec-closeTm α (λ ()) (Table .rl (·tab a b)))
      ∙ Alg.⟦_⟧eqn N (inr (·tab a b)) (λ ())
      ∙ TmRec-closeTm α (λ ()) (Table .rr (·tab a b)) )

    pres- : (a : ⟨ R ⟩) → strMap (R.-_ a) ≡ - strMap a
    pres- a = sym
      ( sym (-Tm strMap (var a))
      ∙ sym (TmRec-closeTm α (λ ()) (Table .rl (-tab a)))
      ∙ Alg.⟦_⟧eqn N (inr (-tab a)) (λ ())
      ∙ TmRec-closeTm α (λ ()) (Table .rr (-tab a)) )

    pres0 : strMap R.0r ≡ 0r
    pres0 = sym
      ( sym (0Tm strMap)
      ∙ sym (TmRec-closeTm α (λ ()) (Table .rl 0tab))
      ∙ Alg.⟦_⟧eqn N (inr 0tab) (λ ())
      ∙ TmRec-closeTm α (λ ()) (Table .rr 0tab) )

    pres1 : strMap R.1r ≡ 1r
    pres1 = sym
      ( sym (1Tm strMap)
      ∙ sym (TmRec-closeTm α (λ ()) (Table .rl 1tab))
      ∙ Alg.⟦_⟧eqn N (inr 1tab) (λ ())
      ∙ TmRec-closeTm α (λ ()) (Table .rr 1tab) )

  -- R[V] is itself a commutative ring, and its coefficients form a ring
  -- homomorphism R → R[V].
  module _ (V : Type ℓ) where
    private
      R[V]hSet : hSet (ℓ-suc ℓ)
      R[V]hSet = R[V] V , trunc

    R[V]Base : Alg (CommRingEqns ℓ) (R[V] V)
    R[V]Base = baseAlg R[V]hSet (R[V]Alg V)

    open CommRingNotation R[V]Base

    R[V]CommRingStr : CommRingStr (R[V] V)
    R[V]CommRingStr .CommRingStr.0r = 0r
    R[V]CommRingStr .CommRingStr.1r = 1r
    R[V]CommRingStr .CommRingStr._+_ = _+_
    R[V]CommRingStr .CommRingStr._·_ = _·_
    R[V]CommRingStr .CommRingStr.-_ = -_
    R[V]CommRingStr .CommRingStr.isCommRing =
      makeIsCommRing trunc +Assoc +IdR +InvR +Comm ·Assoc ·IdR
        ·DistR+ ·Comm

    R[V]CommRing : CommRing (ℓ-suc ℓ)
    R[V]CommRing = R[V] V , R[V]CommRingStr

    coeffPres+ : (a b : ⟨ R ⟩)
      → coeff V (R._+_ a b) ≡ coeff V a + coeff V b
    coeffPres+ = pres+ R[V]hSet (R[V]Alg V)

    coeffPres· : (a b : ⟨ R ⟩)
      → coeff V (R._·_ a b) ≡ coeff V a · coeff V b
    coeffPres· = pres· R[V]hSet (R[V]Alg V)

    coeffPres- : (a : ⟨ R ⟩) → coeff V (R.-_ a) ≡ - coeff V a
    coeffPres- = pres- R[V]hSet (R[V]Alg V)

    coeffPres0 : coeff V R.0r ≡ 0r
    coeffPres0 = pres0 R[V]hSet (R[V]Alg V)

    coeffPres1 : coeff V R.1r ≡ 1r
    coeffPres1 = pres1 R[V]hSet (R[V]Alg V)
