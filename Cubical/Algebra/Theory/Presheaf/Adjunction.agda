-- The free/forgetful adjunction for PRESHEAF-VALUED models of an
-- algebraic theory: the presheaf analogue of
-- `Cubical.Algebra.Theory.Free.Adjunction`.
--
-- `Presheaf/Free.agda` proves the universal property `UPPMod`: model
-- homomorphisms out of the free presheaf model on `P : Presheaf C ℓv`
-- are strict presheaf morphisms out of `P`.  This file packages that
-- bijection as a natural isomorphism of hom-sets.
--
-- THE LEVEL SITUATION.  It is exactly the one described at length in
-- `Cubical.Algebra.Theory.Free.Adjunction`, one level up: the free
-- model on `P : Presheaf C ℓv` lives at `ℓF = ℓFree ℓ ℓ'' ℓv`, which
-- contains `ℓ-suc ℓv`, so `FreePshF : Functor (PRESHEAF C ℓv) (PMOD
-- σeq ℓF)` while `ForgetPsh : Functor (PMOD σeq ℓF) (PRESHEAF C ℓF)`.
-- The two do not compose into an endo-adjunction.  What is true is
--
--     PMOD ℓF [ FreePshF P , N ]
--       ≅  PRESHEAF C ℓF [ LiftPRESHEAF P , ForgetPsh N ]
--
-- i.e. `FreePshF` is left adjoint to `ForgetPsh` RELATIVE TO the
-- lifting functor `LiftPRESHEAF = LiftPsh ℓv ℓF` of
-- `Cubical.Categories.Presheaf.StrictHom.Lift`, which was built for
-- precisely this purpose.
--
-- WHY THE UPSTREAM `Adjunction` RECORDS ARE NOT USED.  See the header
-- of `Cubical.Algebra.Theory.Free.Adjunction`: both
-- `Cubical.Categories.Adjoint.NaturalBijection._⊣_` and
-- `...UnitCounit._⊣_` demand `F : Functor C D` and `G : Functor D C`
-- for the same pair `C`, `D`, and upstream has no relative-adjunction
-- notion.  The reasoning applies verbatim here, so the content is
-- again delivered as standalone named theorems: `adjIsoPsh`,
-- `adjNatInPMOD`, `adjNatInPRESHEAF`, `ηPsh`.
--
-- NO COUNIT, HENCE NO TRIANGLE IDENTITIES.  A relative adjunction has
-- a unit but no counit: `ε` would have to be a map out of
-- `FreePshF (ForgetPsh N)`, but `ForgetPsh N` is a presheaf at level
-- `ℓF`, not an object of `PRESHEAF C ℓv`, so `FreePshF ∘ ForgetPsh`
-- does not even typecheck.  The triangle identities are therefore not
-- statable and are not attempted.  What survives is `ηPsh` (an honest
-- `NatTrans LiftPRESHEAF (ForgetPsh ∘ FreePshF)`) together with
-- `♭≡ηPsh⋆` and `♯PshUniq`, which say that `ηPsh` is universal --
-- the usual unit-side content of the triangle laws.
module Cubical.Algebra.Theory.Presheaf.Adjunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.Lift

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Free.Section
open import Cubical.Algebra.Theory.Presheaf.Base
open import Cubical.Algebra.Theory.Presheaf.Free

private
  variable
    ℓ ℓ'' ℓv ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} {σ : AlgTheorySig ℓ ℓv}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) where
  private
    ℓF = ℓFree ℓ ℓ'' ℓv
    module M = Category (PMOD {C = C} σeq ℓF)
    module S = Category (PRESHEAF C ℓF)

  LiftPRESHEAF : Functor (PRESHEAF C ℓv) (PRESHEAF C ℓF)
  LiftPRESHEAF = LiftPsh ℓv ℓF

  adjIsoPsh : (P : Presheaf C ℓv) (N : Category.ob (PMOD {C = C} σeq ℓF))
    → Iso (PMOD {C = C} σeq ℓF [ FreePshF σeq ⟅ P ⟆ , N ])
          (PRESHEAF C ℓF [ LiftPRESHEAF ⟅ P ⟆ , ForgetPsh σeq ⟅ N ⟆ ])
  adjIsoPsh P N =
    compIso (UPPMod σeq P N)
      (invIso (liftHomIso ℓv ℓF P (ForgetPsh σeq ⟅ N ⟆)))

  -- Transposition.  As in the `SET` case neither endpoint is
  -- determined by the hom type, so both are explicit arguments.
  ♭Psh : (P : Presheaf C ℓv) (N : Category.ob (PMOD {C = C} σeq ℓF))
    → PMOD {C = C} σeq ℓF [ FreePshF σeq ⟅ P ⟆ , N ]
    → PRESHEAF C ℓF [ LiftPRESHEAF ⟅ P ⟆ , ForgetPsh σeq ⟅ N ⟆ ]
  ♭Psh P N = adjIsoPsh P N .Iso.fun

  ♯Psh : (P : Presheaf C ℓv) (N : Category.ob (PMOD {C = C} σeq ℓF))
    → PRESHEAF C ℓF [ LiftPRESHEAF ⟅ P ⟆ , ForgetPsh σeq ⟅ N ⟆ ]
    → PMOD {C = C} σeq ℓF [ FreePshF σeq ⟅ P ⟆ , N ]
  ♯Psh P N = adjIsoPsh P N .Iso.inv

  -- Naturality in the model variable (post-composition).
  adjNatInPMOD : (P : Presheaf C ℓv)
    (N N' : Category.ob (PMOD {C = C} σeq ℓF))
    (f : PMOD {C = C} σeq ℓF [ FreePshF σeq ⟅ P ⟆ , N ])
    (k : PMOD {C = C} σeq ℓF [ N , N' ])
    → ♭Psh P N' (M._⋆_ {x = FreePshF σeq ⟅ P ⟆} {y = N} {z = N'} f k)
      ≡ S._⋆_ {x = LiftPRESHEAF ⟅ P ⟆} {y = ForgetPsh σeq ⟅ N ⟆}
          {z = ForgetPsh σeq ⟅ N' ⟆} (♭Psh P N f)
          (Functor.F-hom (ForgetPsh σeq) {x = N} {y = N'} k)
  adjNatInPMOD P N N' f k = refl

  -- Naturality in the presheaf of generators (pre-composition).
  adjNatInPRESHEAF : (P' P : Presheaf C ℓv)
    (N : Category.ob (PMOD {C = C} σeq ℓF))
    (g : PRESHEAF C ℓF [ LiftPRESHEAF ⟅ P ⟆ , ForgetPsh σeq ⟅ N ⟆ ])
    (γ : PRESHEAF C ℓv [ P' , P ])
    → ♯Psh P' N (S._⋆_ {x = LiftPRESHEAF ⟅ P' ⟆} {y = LiftPRESHEAF ⟅ P ⟆}
                   {z = ForgetPsh σeq ⟅ N ⟆}
                   (Functor.F-hom LiftPRESHEAF {x = P'} {y = P} γ) g)
      ≡ M._⋆_ {x = FreePshF σeq ⟅ P' ⟆} {y = FreePshF σeq ⟅ P ⟆} {z = N}
          (Functor.F-hom (FreePshF σeq) {x = P'} {y = P} γ) (♯Psh P N g)
  adjNatInPRESHEAF P' P N g γ =
    isoFunInjective (adjIsoPsh P' N) _ _ (makePshHomStrictPath refl)

  -- The unit.  `LiftPRESHEAF` and `ForgetPsh ∘ FreePshF` are both
  -- functors `PRESHEAF C ℓv → PRESHEAF C ℓF`, so this is an honest
  -- natural transformation; it is `genPsh` modulo the lift.
  ηPsh : NatTrans LiftPRESHEAF (funcComp (ForgetPsh σeq) (FreePshF σeq))
  ηPsh .NatTrans.N-ob P .PshHomStrict.N-ob c x =
    genPsh σeq P .PshHomStrict.N-ob c (x .lower)
  ηPsh .NatTrans.N-ob P .PshHomStrict.N-hom c c' f p' p e =
    genPsh σeq P .PshHomStrict.N-hom c c' f (p' .lower) (p .lower)
      (cong lower e)
  -- Unlike the `SET` case, `N-hom` is NOT `refl`: the two sides agree
  -- on `N-ob` definitionally, but their forded naturality witnesses do
  -- not, so the path is `makePshHomStrictPath refl` (the same
  -- asymmetry as in `FreePshF`'s `F-id`/`F-seq`).
  ηPsh .NatTrans.N-hom γ = makePshHomStrictPath refl

  -- The transpose is `ηPsh` followed by the forgotten map.
  ♭≡ηPsh⋆ : (P : Presheaf C ℓv) (N : Category.ob (PMOD {C = C} σeq ℓF))
    (f : PMOD {C = C} σeq ℓF [ FreePshF σeq ⟅ P ⟆ , N ])
    → ♭Psh P N f
      ≡ S._⋆_ {x = LiftPRESHEAF ⟅ P ⟆}
          {y = ForgetPsh σeq ⟅ FreePshF σeq ⟅ P ⟆ ⟆}
          {z = ForgetPsh σeq ⟅ N ⟆} (ηPsh .NatTrans.N-ob P)
          (Functor.F-hom (ForgetPsh σeq) {x = FreePshF σeq ⟅ P ⟆} {y = N} f)
  ♭≡ηPsh⋆ P N f = refl

  -- ... and `♯Psh` is the unique fill, which is exactly `Iso.ret`.
  ♯PshUniq : (P : Presheaf C ℓv) (N : Category.ob (PMOD {C = C} σeq ℓF))
    (f : PMOD {C = C} σeq ℓF [ FreePshF σeq ⟅ P ⟆ , N ])
    → ♯Psh P N (♭Psh P N f) ≡ f
  ♯PshUniq P N = adjIsoPsh P N .Iso.ret
