-- Free presheaf-valued models of a many-sorted theory, their
-- universal property, and initiality.
--
-- `Sorted.agda` gives the free model on a *sorted set* `(V , vs)`.
-- The base of the model tower is `FAM S ℓX`, whose objects are
-- S-indexed families, so the first thing to do is to turn the free
-- model into a functor on families; the generators of the free model
-- on `X` are the total sorted set `Σ[ s ∈ S ] ⟨ X s ⟩`.  This forces
-- the variable level of the theory to be `ℓ-max ℓS ℓX`, exactly as
-- the single-sorted presheaf file forces it to be the level of the
-- presheaf of generators.
module Cubical.Algebra.Theory.Sorted.Presheaf.Free where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥* ; isProp⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base

open import Cubical.Algebra.Theory.Sorted
open import Cubical.Algebra.Theory.Sorted.Presheaf.Base

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓY ℓC ℓC' : Level

open Functor
open PshAlgˢ
open PshHomStrict
open SortedSig
open SortedEqns

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {ℓX : Level}
  (σeq : SortedEqns σ ℓ'' (ℓ-max ℓS ℓX)) where

  private
    ℓF = ℓFree ℓS ℓ ℓ' ℓ'' (ℓ-max ℓS ℓX)

  -- The generators of the free model on a family: its total sorted set.
  ΣFam : (X : S → hSet ℓX) → Type (ℓ-max ℓS ℓX)
  ΣFam X = Σ[ s ∈ S ] ⟨ X s ⟩

  FreeFamOb : (X : S → hSet ℓX) → Category.ob (MOD σeq ℓF)
  FreeFamOb X = FreeOb σeq (ΣFam X) fst

  -- The free functor on families.  Both laws are `refl` after the
  -- universal property, since `gen` is a constructor.
  FreeFamF : Functor (FAM S ℓX) (MOD σeq ℓF)
  FreeFamF .F-ob = FreeFamOb
  FreeFamF .F-hom {x = X} {y = Y} f =
    Iso.inv (UPMod σeq (ΣFam X) fst (FreeFamOb Y))
      (λ v → gen (v .fst , f (v .fst) (v .snd)))
  FreeFamF .F-id {x = X} =
    isoFunInjective (UPMod σeq (ΣFam X) fst (FreeFamOb X)) _ _ refl
  FreeFamF .F-seq {x = X} {z = Z} f g =
    isoFunInjective (UPMod σeq (ΣFam X) fst (FreeFamOb Z)) _ _ refl

  module _ {C : Category ℓC ℓC'} where

    -- An S-indexed family of presheaves, read as a presheaf of
    -- families.  This is the only place the two shapes of the base
    -- have to be reconciled, and it costs one `funExt` per law.
    FamPsh : (P : S → Presheaf C ℓX) → Functor (C ^op) (FAM S ℓX)
    FamPsh P .F-ob c s = P s ⟅ c ⟆
    FamPsh P .F-hom f s = P s ⟪ f ⟫
    FamPsh P .F-id = funExt (λ s → P s .F-id)
    FamPsh P .F-seq f g = funExt (λ s → P s .F-seq f g)

    -- The free model on a family of presheaves is pointwise, and its
    -- restriction maps are `FreeFamF`'s action on `P`'s.
    FreePshMod : (P : S → Presheaf C ℓX) → Functor (C ^op) (MOD σeq ℓF)
    FreePshMod P = funcComp FreeFamF (FamPsh P)

    FreePshOb : (P : S → Presheaf C ℓX) → Category.ob (PMOD σeq ℓF)
    FreePshOb P = Mod→PMod σeq (FreePshMod P)

    -- The generators.  Naturality holds because `FreeFamF`'s action
    -- sends a generator to a generator.
    genPsh : (P : S → Presheaf C ℓX) (s : S)
      → PshHomStrict (P s) ((ForgetPsh σeq ⟅ FreePshOb P ⟆) s)
    genPsh P s .N-ob c p = gen (s , p)
    genPsh P s .N-hom c c' f p' p eq = cong (λ q → gen (s , q)) eq

    -- The universal property.  Pointwise it is `UPMod`; the extra
    -- content is that the pointwise extensions are automatically
    -- natural, which is `UPMod`'s uniqueness applied to the naturality
    -- square.
    module _ (P : S → Presheaf C ℓX)
      (N : Category.ob (PMOD {C = C} σeq ℓF)) where
      private
        module M = Category (MOD σeq ℓF)

        NM : Functor (C ^op) (MOD σeq ℓF)
        NM = PMod→Mod σeq N

        Gen : Category.ob C → Type (ℓ-max ℓS ℓX)
        Gen c = ΣFam (FamPsh P ⟅ c ⟆)

      module _ (β : (s : S)
                  → PshHomStrict (P s) ((ForgetPsh σeq ⟅ N ⟆) s)) where
        private
          ext : (c : Category.ob C)
            → ModHom σeq ℓF (FreePshMod P ⟅ c ⟆) (NM ⟅ c ⟆)
          ext c = Iso.inv (UPMod σeq (Gen c) fst (NM ⟅ c ⟆))
            (λ v → β (v .fst) .N-ob c (v .snd))

          natSq : {c c' : Category.ob C} (f : C [ c , c' ])
            → M._⋆_ {x = FreePshMod P ⟅ c' ⟆} {y = FreePshMod P ⟅ c ⟆}
                {z = NM ⟅ c ⟆} (FreePshMod P ⟪ f ⟫) (ext c)
              ≡ M._⋆_ {x = FreePshMod P ⟅ c' ⟆} {y = NM ⟅ c' ⟆}
                {z = NM ⟅ c ⟆} (ext c') (NM ⟪ f ⟫)
          natSq {c} {c'} f =
            isoFunInjective (UPMod σeq (Gen c') fst (NM ⟅ c ⟆)) _ _
              (funExt (λ v →
                sym (β (v .fst) .N-hom c c' f (v .snd) _ refl)))

        UPPModInv : PModHom σeq ℓF (FreePshOb P) N
        UPPModInv .fst s .N-ob c t = ext c .fst s t
        UPPModInv .fst s .N-hom c c' f t' t eq =
          sym (funExt⁻ (funExt⁻ (cong fst (natSq f)) s) t')
          ∙ cong (ext c .fst s) eq
        UPPModInv .snd c = ext c .snd .fst

      UPPMod : Iso (PModHom σeq ℓF (FreePshOb P) N)
                   ((s : S) → PshHomStrict (P s)
                                ((ForgetPsh σeq ⟅ N ⟆) s))
      UPPMod .Iso.fun (α , ϕ) s = genPsh P s ⋆PshHomStrict α s
      UPPMod .Iso.inv = UPPModInv
      UPPMod .Iso.sec β = funExt (λ s → makePshHomStrictPath refl)
      UPPMod .Iso.ret (α , ϕ) =
        Σ≡Prop
          (λ _ → isPropΠ (λ c → isPropΠ4 (λ o _ _ _ →
            str ((N .fst (σ .resultSort o)) ⟅ c ⟆) _ _)))
          (funExt (λ s → makePshHomStrictPath (funExt (λ c →
            funExt⁻ (cong fst (Iso.ret (UPMod σeq (Gen c) fst (NM ⟅ c ⟆))
              ((λ s' → α s' .N-ob c) , ϕ c , tt*))) s))))

    -- Initiality is the case of no generators: the free model on the
    -- empty family of presheaves.
    EmptyPsh : S → Presheaf C ℓX
    EmptyPsh s .F-ob _ = ⊥* , isProp→isSet isProp⊥*
    EmptyPsh s .F-hom _ ()
    EmptyPsh s .F-id = funExt (λ ())
    EmptyPsh s .F-seq _ _ = funExt (λ ())

    isContrEmptyHom : (Q : S → Presheaf C ℓY)
      → isContr ((s : S) → PshHomStrict (EmptyPsh s) (Q s))
    isContrEmptyHom Q .fst s .N-ob c ()
    isContrEmptyHom Q .fst s .N-hom c c' f ()
    isContrEmptyHom Q .snd α =
      funExt (λ s → makePshHomStrictPath (funExt (λ c → funExt (λ ()))))

    isInitialFreePshOb :
      isInitial (PMOD {C = C} σeq ℓF) (FreePshOb EmptyPsh)
    isInitialFreePshOb N =
      isOfHLevelRetractFromIso 0 (UPPMod EmptyPsh N)
        (isContrEmptyHom (ForgetPsh σeq ⟅ N ⟆))

    InitialPMOD : Initial (PMOD {C = C} σeq ℓF)
    InitialPMOD = FreePshOb EmptyPsh , isInitialFreePshOb

    -- The free functor.  As in the SET case the levels do not match up
    -- into an endo-adjunction: `FreePshF` lands at `ℓF`, strictly
    -- above the level `ℓX` of its argument.
    FreePshF : Functor (FAMPSH S C ℓX) (PMOD {C = C} σeq ℓF)
    FreePshF .F-ob = FreePshOb
    FreePshF .F-hom {x = P} {y = Q} α =
      Iso.inv (UPPMod P (FreePshOb Q))
        (λ s → α s ⋆PshHomStrict genPsh Q s)
    FreePshF .F-id {x = P} =
      isoFunInjective (UPPMod P (FreePshOb P)) _ _
        (funExt (λ s → makePshHomStrictPath refl))
    FreePshF .F-seq {x = P} {z = R} α β =
      isoFunInjective (UPPMod P (FreePshOb R)) _ _
        (funExt (λ s → makePshHomStrictPath refl))
