-- The free/forgetful adjunction for an algebraic theory.
--
-- `Section.agda` proves the universal property `UPMod`: model
-- homomorphisms out of the free model on `V : Type ℓv` are functions
-- out of `V`.  This file packages that bijection as a functor plus a
-- natural isomorphism of hom-sets.
--
-- THE LEVEL SITUATION.  The free model on `V : Type ℓv` lives at
-- `ℓF = ℓFree ℓ ℓ'' ℓv`, which contains `ℓ-suc ℓv`, so `ℓF` is
-- strictly above `ℓv`.  Hence `FreeF : Functor (SET ℓv) (MOD σeq ℓF)`
-- while `Forget : Functor (MOD σeq ℓF) (SET ℓF)`: the two functors do
-- not compose into an endo-adjunction, and there is no `Free ⊣ Forget`
-- on a single `SET`.  What is true is the bijection
--
--     MOD ℓF [ FreeF V , N ]  ≅  SET ℓF [ LiftSET V , Forget N ]
--
-- i.e. `FreeF` is left adjoint to `Forget` RELATIVE TO the lifting
-- functor `LiftSET = LiftF ℓF : Functor (SET ℓv) (SET ℓF)`.
--
-- WHY THE UPSTREAM `Adjunction` RECORD IS NOT USED.  Both
-- `Cubical.Categories.Adjoint.NaturalBijection._⊣_` and
-- `...UnitCounit._⊣_` require `F : Functor C D` and `G : Functor D C`
-- for the *same* pair `C`, `D`.  Taking `C = SET ℓv` and
-- `D = MOD σeq ℓF` forces `G : Functor (MOD σeq ℓF) (SET ℓv)`, but
-- `Forget` lands in `SET ℓF`, and there is no functor
-- `SET ℓF → SET ℓv`.  Upstream has no relative-adjunction notion
-- (nothing in `Cubical/Categories/` mentions one), so the content is
-- delivered here as standalone named theorems: `FreeF`, `adjIso`,
-- `adjNatInMOD`, `adjNatInSET`.
--
-- CONSEQUENCE FOR THE TRIANGLE IDENTITIES.  A relative adjunction has
-- a unit but no counit: `ε` would have to be a map out of
-- `FreeF (Forget N)`, and `Forget N : hSet ℓF` is not an object of
-- `SET ℓv`, so `FreeF ∘ Forget` does not typecheck.  The triangle
-- identities are therefore not even statable.  What survives is `η`
-- (an honest `NatTrans LiftSET (Forget ∘F FreeF)`) together with
-- `♭≡η⋆` and `♯Uniq`, which say that `η` is universal -- the usual
-- unit-side content of the triangle laws.
module Cubical.Algebra.Theory.Free.Adjunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Category
open import Cubical.Algebra.Theory.Free.Explicit
open import Cubical.Algebra.Theory.Free.Section

private
  variable
    ℓ ℓ'' ℓv : Level

module _ {σ : AlgTheorySig ℓ ℓv} (σeq : AlgTheoryEqns σ ℓ'' ℓv) where
  private
    ℓF = ℓFree ℓ ℓ'' ℓv
    module M = Category (MOD σeq ℓF)
    module S = Category (SET ℓF)

  FreeF : Functor (SET ℓv) (MOD σeq ℓF)
  FreeF .Functor.F-ob V = FreeOb σeq ⟨ V ⟩
  FreeF .Functor.F-hom {x = V} {y = W} f =
    Iso.inv (UPMod σeq ⟨ V ⟩ (FreeOb σeq ⟨ W ⟩)) (λ v → gen σeq ⟨ W ⟩ (f v))
  FreeF .Functor.F-id {x = V} =
    isoFunInjective (UPMod σeq ⟨ V ⟩ (FreeOb σeq ⟨ V ⟩)) _ _ refl
  FreeF .Functor.F-seq {x = V} {y = W} {z = U} f g =
    isoFunInjective (UPMod σeq ⟨ V ⟩ (FreeOb σeq ⟨ U ⟩)) _ _ refl

  -- The lifting functor along which the adjunction is relative.
  LiftSET : Functor (SET ℓv) (SET ℓF)
  LiftSET = LiftF ℓF

  private
    liftDomIso : (V : hSet ℓv) (A : Type ℓF)
      → Iso (⟨ V ⟩ → A) (Lift ℓF ⟨ V ⟩ → A)
    liftDomIso V A .Iso.fun g x = g (x .lower)
    liftDomIso V A .Iso.inv h v = h (lift v)
    liftDomIso V A .Iso.sec h = refl
    liftDomIso V A .Iso.ret g = refl

  adjIso : (V : hSet ℓv) (N : Category.ob (MOD σeq ℓF))
    → Iso (MOD σeq ℓF [ FreeF ⟅ V ⟆ , N ])
          (SET ℓF [ LiftSET ⟅ V ⟆ , Forget σeq ⟅ N ⟆ ])
  adjIso V N =
    compIso (UPMod σeq ⟨ V ⟩ N) (liftDomIso V ⟨ N .fst ⟩)

  -- Transposition.  `FreeF ⟅ V ⟆` and `N` do not determine each other,
  -- so both are explicit arguments.
  ♭ : (V : hSet ℓv) (N : Category.ob (MOD σeq ℓF))
    → MOD σeq ℓF [ FreeF ⟅ V ⟆ , N ]
    → SET ℓF [ LiftSET ⟅ V ⟆ , Forget σeq ⟅ N ⟆ ]
  ♭ V N = adjIso V N .Iso.fun

  ♯ : (V : hSet ℓv) (N : Category.ob (MOD σeq ℓF))
    → SET ℓF [ LiftSET ⟅ V ⟆ , Forget σeq ⟅ N ⟆ ]
    → MOD σeq ℓF [ FreeF ⟅ V ⟆ , N ]
  ♯ V N = adjIso V N .Iso.inv

  -- Naturality in the model variable (post-composition).  Objects of
  -- `SET`/`MOD` are not determined by their hom types (a `SET` hom is a
  -- bare function), so every composite pins its endpoints explicitly.
  adjNatInMOD : (V : hSet ℓv) (N N' : Category.ob (MOD σeq ℓF))
    (f : MOD σeq ℓF [ FreeF ⟅ V ⟆ , N ]) (k : MOD σeq ℓF [ N , N' ])
    → ♭ V N' (M._⋆_ {x = FreeF ⟅ V ⟆} {y = N} {z = N'} f k)
      ≡ S._⋆_ {x = LiftSET ⟅ V ⟆} {y = Forget σeq ⟅ N ⟆}
          {z = Forget σeq ⟅ N' ⟆} (♭ V N f)
          (Functor.F-hom (Forget σeq) {x = N} {y = N'} k)
  adjNatInMOD V N N' f k = refl

  -- Naturality in the set of generators (pre-composition).
  adjNatInSET : (V' V : hSet ℓv) (N : Category.ob (MOD σeq ℓF))
    (g : SET ℓF [ LiftSET ⟅ V ⟆ , Forget σeq ⟅ N ⟆ ])
    (h : SET ℓv [ V' , V ])
    → ♯ V' N (S._⋆_ {x = LiftSET ⟅ V' ⟆} {y = LiftSET ⟅ V ⟆}
                {z = Forget σeq ⟅ N ⟆}
                (Functor.F-hom LiftSET {x = V'} {y = V} h) g)
      ≡ M._⋆_ {x = FreeF ⟅ V' ⟆} {y = FreeF ⟅ V ⟆} {z = N}
          (Functor.F-hom FreeF {x = V'} {y = V} h) (♯ V N g)
  adjNatInSET V' V N g h =
    isoFunInjective (adjIso V' N) _ _ refl

  -- The unit.  Both `LiftSET` and `Forget ∘ FreeF` are functors
  -- `SET ℓv → SET ℓF`, so this is an honest natural transformation;
  -- it is `gen` modulo the lift.
  η : NatTrans LiftSET (funcComp (Forget σeq) FreeF)
  η .NatTrans.N-ob V x = gen σeq ⟨ V ⟩ (x .lower)
  η .NatTrans.N-hom h = refl

  -- The transpose is `η` followed by the forgotten map: the usual
  -- formula, here definitional.
  ♭≡η⋆ : (V : hSet ℓv) (N : Category.ob (MOD σeq ℓF))
    (f : MOD σeq ℓF [ FreeF ⟅ V ⟆ , N ])
    → ♭ V N f
      ≡ S._⋆_ {x = LiftSET ⟅ V ⟆} {y = Forget σeq ⟅ FreeF ⟅ V ⟆ ⟆}
          {z = Forget σeq ⟅ N ⟆} (η .NatTrans.N-ob V)
          (Functor.F-hom (Forget σeq) {x = FreeF ⟅ V ⟆} {y = N} f)
  ♭≡η⋆ V N f = refl

  -- ... and `♯` is the unique fill, which is exactly `Iso.ret`.
  ♯Uniq : (V : hSet ℓv) (N : Category.ob (MOD σeq ℓF))
    (f : MOD σeq ℓF [ FreeF ⟅ V ⟆ , N ]) → ♯ V N (♭ V N f) ≡ f
  ♯Uniq V N = adjIso V N .Iso.ret
