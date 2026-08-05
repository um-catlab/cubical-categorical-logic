-- Free presheaf-valued models, their universal property, and initiality.
module Cubical.Algebra.Theory.Presheaf.Free where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥* ; isProp⊥*)
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Category
open import Cubical.Algebra.Theory.Free.Explicit
open import Cubical.Algebra.Theory.Free.Section
open import Cubical.Algebra.Theory.Free.Adjunction
open import Cubical.Algebra.Theory.Presheaf.Base

private
  variable
    ℓ ℓ' ℓ'' ℓv ℓX ℓC ℓC' : Level

open Functor
open PshAlg
open PshHomStrict

-- A presheaf-valued model is the same data as a functor into MOD: the
-- fibrewise algebras are the values and the `restr` homomorphisms are
-- the functorial action.
module _ {C : Category ℓC ℓC'} {σ : AlgTheorySig ℓ ℓ'}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) where

  Mod→PMod : (M : Functor (C ^op) (MOD σeq ℓX))
    → Category.ob (PMOD {C = C} σeq ℓX)
  Mod→PMod M .fst = funcComp (Forget σeq) M
  Mod→PMod M .snd .alg c = (M ⟅ c ⟆) .snd
  Mod→PMod M .snd .restr f = (M ⟪ f ⟫) .snd

  PMod→Mod : (N : Category.ob (PMOD {C = C} σeq ℓX))
    → Functor (C ^op) (MOD σeq ℓX)
  PMod→Mod N .F-ob c = (N .fst ⟅ c ⟆) , N .snd .alg c
  PMod→Mod N .F-hom f = (N .fst ⟪ f ⟫) , N .snd .restr f
  PMod→Mod N .F-id =
    Σ≡Prop (λ _ → isPropHomo σeq (str (N .fst ⟅ _ ⟆))) (N .fst .F-id)
  PMod→Mod N .F-seq f g =
    Σ≡Prop (λ _ → isPropHomo σeq (str (N .fst ⟅ _ ⟆))) (N .fst .F-seq f g)

-- From here on the arity level must agree with the variable level, as
-- for the free model in `Free.Explicit`.
module _ {C : Category ℓC ℓC'} {σ : AlgTheorySig ℓ ℓv}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) where
  private
    ℓF = ℓFree ℓ ℓ'' ℓv

  -- The free model on a presheaf is pointwise: `FreeF` applied to `P`.
  -- Functoriality of the restriction maps is `FreeF`'s.
  FreePshMod : (P : Presheaf C ℓv) → Functor (C ^op) (MOD σeq ℓF)
  FreePshMod P = funcComp (FreeF σeq) P

  FreePshOb : (P : Presheaf C ℓv) → Category.ob (PMOD {C = C} σeq ℓF)
  FreePshOb P = Mod→PMod σeq (FreePshMod P)

  -- The generators.  Naturality is `FreeF`'s action on `P`'s own
  -- restriction maps, which sends a variable to a variable.
  genPsh : (P : Presheaf C ℓv)
    → PshHomStrict P (ForgetPsh σeq ⟅ FreePshOb P ⟆)
  genPsh P .N-ob c = gen σeq ⟨ P ⟅ c ⟆ ⟩
  genPsh P .N-hom c c' f p' p eq = cong (gen σeq ⟨ P ⟅ c ⟆ ⟩) eq

  -- The universal property.  Pointwise it is `UPMod`; the extra content
  -- is that the pointwise extensions are automatically natural, which
  -- is `UPMod`'s uniqueness applied to the naturality square.
  module _ (P : Presheaf C ℓv) (N : Category.ob (PMOD {C = C} σeq ℓF)) where
    private
      module P = PresheafNotation P
      module M = Category (MOD σeq ℓF)

      NM : Functor (C ^op) (MOD σeq ℓF)
      NM = PMod→Mod σeq N

    module _ (β : PshHomStrict P (ForgetPsh σeq ⟅ N ⟆)) where
      private
        ext : ∀ c → ModHom σeq ℓF (FreeOb σeq ⟨ P ⟅ c ⟆ ⟩) (NM ⟅ c ⟆)
        ext c = Iso.inv (UPMod σeq ⟨ P ⟅ c ⟆ ⟩ (NM ⟅ c ⟆)) (β .N-ob c)

        natSq : ∀ {c c'} (f : C [ c , c' ])
          → M._⋆_ {x = FreePshMod P ⟅ c' ⟆} {y = FreePshMod P ⟅ c ⟆}
              {z = NM ⟅ c ⟆} (FreePshMod P ⟪ f ⟫) (ext c)
            ≡ M._⋆_ {x = FreePshMod P ⟅ c' ⟆} {y = NM ⟅ c' ⟆} {z = NM ⟅ c ⟆}
              (ext c') (NM ⟪ f ⟫)
        natSq {c} {c'} f =
          isoFunInjective (UPMod σeq ⟨ P ⟅ c' ⟆ ⟩ (NM ⟅ c ⟆)) _ _
            (funExt (λ p' → sym (β .N-hom c c' f p' (f P.⋆ p') refl)))

      UPPModInv : PModHom σeq ℓF (FreePshOb P) N
      UPPModInv .fst .N-ob c = ext c .fst
      UPPModInv .fst .N-hom c c' f t' t eq =
        sym (funExt⁻ (cong fst (natSq f)) t') ∙ cong (ext c .fst) eq
      UPPModInv .snd c = ext c .snd

    UPPMod : Iso (PModHom σeq ℓF (FreePshOb P) N)
                 (PshHomStrict P (ForgetPsh σeq ⟅ N ⟆))
    UPPMod .Iso.fun (α , ϕ) = genPsh P ⋆PshHomStrict α
    UPPMod .Iso.inv = UPPModInv
    UPPMod .Iso.sec β = makePshHomStrictPath refl
    UPPMod .Iso.ret (α , ϕ) =
      Σ≡Prop (λ _ → isPropΠ (λ c → isPropHomo σeq (str (N .fst ⟅ c ⟆))))
        (makePshHomStrictPath (funExt (λ c →
          cong fst (Iso.ret (UPMod σeq ⟨ P ⟅ c ⟆ ⟩ (NM ⟅ c ⟆))
            (α .N-ob c , ϕ c)))))

  -- Initiality is the case of no generators: the free model on the
  -- empty presheaf.
  EmptyPsh : Presheaf C ℓv
  EmptyPsh .F-ob _ = ⊥* , isProp→isSet isProp⊥*
  EmptyPsh .F-hom _ ()
  EmptyPsh .F-id = funExt (λ ())
  EmptyPsh .F-seq _ _ = funExt (λ ())

  isContrPshHomStrictEmpty : (Q : Presheaf C ℓX)
    → isContr (PshHomStrict EmptyPsh Q)
  isContrPshHomStrictEmpty Q .fst .N-ob c ()
  isContrPshHomStrictEmpty Q .fst .N-hom c c' f ()
  isContrPshHomStrictEmpty Q .snd α =
    makePshHomStrictPath (funExt (λ c → funExt (λ ())))

  isInitialFreePshOb : isInitial (PMOD {C = C} σeq ℓF) (FreePshOb EmptyPsh)
  isInitialFreePshOb N =
    isOfHLevelRetractFromIso 0 (UPPMod EmptyPsh N)
      (isContrPshHomStrictEmpty (ForgetPsh σeq ⟅ N ⟆))

  InitialPMOD : Initial (PMOD {C = C} σeq ℓF)
  InitialPMOD = FreePshOb EmptyPsh , isInitialFreePshOb

  -- The free functor.  As in the SET case the levels do not match up
  -- into an endo-adjunction: `FreePshF` lands at `ℓF`, strictly above
  -- the level `ℓv` of its argument.
  FreePshF : Functor (PRESHEAF C ℓv) (PMOD {C = C} σeq ℓF)
  FreePshF .F-ob = FreePshOb
  FreePshF .F-hom {x = P} {y = Q} α =
    Iso.inv (UPPMod P (FreePshOb Q)) (α ⋆PshHomStrict genPsh Q)
  FreePshF .F-id {x = P} =
    isoFunInjective (UPPMod P (FreePshOb P)) _ _
      (makePshHomStrictPath refl)
  FreePshF .F-seq {x = P} {y = Q} {z = R} α β =
    isoFunInjective (UPPMod P (FreePshOb R)) _ _
      (makePshHomStrictPath refl)
