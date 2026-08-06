-- Presheaf-valued models of a *many-sorted* algebraic theory,
-- displayed over the S-indexed product of the strict-hom presheaf
-- category.
--
-- This is the sorted analogue of `Theory.Presheaf.Base`.  The base is
-- to `PRESHEAF` what `FAM S ℓX` is to `SET ℓX`: an S-indexed family of
-- presheaves, with homomorphisms taken sortwise.  Everything else
-- ports unchanged, because the two facts the single-sorted
-- construction rests on -- that the homomorphism condition of `ALGᴰ`
-- and the naturality condition `PshHomStrict.N-hom` are both forded --
-- hold verbatim in the sorted case.
module Cubical.Algebra.Theory.Sorted.Presheaf.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base

open import Cubical.Algebra.Theory.Sorted

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX ℓY ℓC ℓC' : Level

open Category
open SortedSig
open SortedEqns

-- The base of the tower: S-indexed families of presheaves, the
-- S-indexed product of `PRESHEAF C ℓX`.
FAMPSH : (S : Type ℓS) (C : Category ℓC ℓC') (ℓX : Level)
  → Category (ℓ-max ℓS (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓX)))
             (ℓ-max ℓS (ℓ-max (ℓ-max ℓC ℓC') ℓX))
FAMPSH S C ℓX .ob = S → Presheaf C ℓX
FAMPSH S C ℓX .Hom[_,_] P Q = (s : S) → PshHomStrict (P s) (Q s)
FAMPSH S C ℓX .id s = idPshHomStrict
FAMPSH S C ℓX ._⋆_ α β s = α s ⋆PshHomStrict β s
FAMPSH S C ℓX .⋆IdL α = refl
FAMPSH S C ℓX .⋆IdR α = refl
FAMPSH S C ℓX .⋆Assoc α β γ = refl
FAMPSH S C ℓX .isSetHom = isSetΠ (λ s → isSetPshHomStrict _ _)

-- The homomorphism condition of `ALGᴰ`, on bare families rather than
-- families of sets, so that it can be stated at a presheaf's value.
-- It is *definitionally* `ALGᴰ σ ℓX .Hom[_][_,_]` at families of sets.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} where

  Homoˢ : {X : S → Type ℓX} {Y : S → Type ℓY}
    (f : (s : S) → X s → Y s)
    (α : Ops {σ = σ} X) (β : Ops {σ = σ} Y) → Type _
  Homoˢ {X = X} f α β =
    (o : σ .ops) (x : (a : σ .arities o) → X (σ .sortOf o a))
    (y : X (σ .resultSort o)) → y ≡ α o x
    → f (σ .resultSort o) y ≡ β o (λ a → f (σ .sortOf o a) (x a))

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {C : Category ℓC ℓC'}
  (σeq : SortedEqns σ ℓ'' ℓv) where

  -- A model of σeq valued in S-indexed families of presheaves over C:
  -- a fibrewise sorted model whose restriction maps are homomorphisms.
  -- `Homoˢ` is forded, so this record carries no non-forded equations
  -- beyond the equations of the theory itself.
  record PshAlgˢ (P : S → Presheaf C ℓX)
    : Type (ℓ-max (ℓ-max ℓC ℓC')
             (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max (ℓ-max ℓ'' ℓv) ℓX))) where
    field
      alg : (c : C .ob) → Ops {σ = σ} (λ s → ⟨ P s ⟅ c ⟆ ⟩)
      sat : (c : C .ob) (e : σeq .eqns)
        (ρ : (v : σeq .vars e) → ⟨ P (σeq .varSort e v) ⟅ c ⟆ ⟩)
        → TmRec (λ s → ⟨ P s ⟅ c ⟆ ⟩) (alg c) ρ (σeq .lhs e)
          ≡ TmRec (λ s → ⟨ P s ⟅ c ⟆ ⟩) (alg c) ρ (σeq .rhs e)
      restr : {c c' : C .ob} (f : C [ c , c' ])
        → Homoˢ (λ s → P s ⟪ f ⟫) (alg c') (alg c)

  open PshAlgˢ
  open PshHomStrict

  -- A homomorphism of presheaf models over a sortwise family of strict
  -- presheaf morphisms is a *bare family* of algebra homomorphisms:
  -- naturality already lives in the base.
  PshAlgHomoˢ : {P Q : S → Presheaf C ℓX}
    (α : (s : S) → PshHomStrict (P s) (Q s))
    (B : PshAlgˢ P) (D : PshAlgˢ Q) → Type _
  PshAlgHomoˢ α B D =
    (c : C .ob) → Homoˢ (λ s → α s .N-ob c) (B .alg c) (D .alg c)

  PMODᴰ : (ℓX : Level) → Categoryᴰ (FAMPSH S C ℓX) _ _
  PMODᴰ ℓX .Categoryᴰ.ob[_] P = PshAlgˢ P
  PMODᴰ ℓX .Categoryᴰ.Hom[_][_,_] α B D = PshAlgHomoˢ α B D
  -- `Homoˢ` is a Π-type rather than a record, so combinators for it
  -- would leave their carrier implicits stuck at these use sites; as
  -- in `ALGᴰ`, the two clauses are written out instead.
  PMODᴰ ℓX .Categoryᴰ.idᴰ c o x y eq = eq
  PMODᴰ ℓX .Categoryᴰ._⋆ᴰ_ {f = α} ϕ ψ c o x y eq =
    ψ c o (λ a → α (σ .sortOf o a) .N-ob c (x a))
      (α (σ .resultSort o) .N-ob c y) (ϕ c o x y eq)
  PMODᴰ ℓX .Categoryᴰ.⋆IdLᴰ fᴰ = refl
  PMODᴰ ℓX .Categoryᴰ.⋆IdRᴰ fᴰ = refl
  PMODᴰ ℓX .Categoryᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ = refl
  PMODᴰ ℓX .Categoryᴰ.isSetHomᴰ {y = Q} =
    isSetΠ λ c → isSetΠ3 λ o x y →
      isSet→ (isProp→isSet (str (Q (σ .resultSort o) ⟅ c ⟆) _ _))

  PMOD : (ℓX : Level) → Category _ _
  PMOD ℓX = ∫C (PMODᴰ ℓX)

  -- a homomorphism of presheaf models
  PModHom : (ℓX : Level) (M N : Category.ob (PMOD ℓX)) → Type _
  PModHom ℓX M N = PMOD ℓX [ M , N ]

  ForgetPsh : Functor (PMOD ℓX) (FAMPSH S C ℓX)
  ForgetPsh = Fst

  -- The bridge.  A presheaf-valued model is the same data as a functor
  -- into `MOD`: the fibrewise models are the values and the `restr`
  -- homomorphisms are the functorial action.  Both directions are the
  -- identity on all the *data*; only the functor laws, which are
  -- propositional, have to be produced.
  module _ (M : Functor (C ^op) (MOD σeq ℓX)) where
    open Functor

    Mod→PMod : Category.ob (PMOD ℓX)
    Mod→PMod .fst s .F-ob c = (M ⟅ c ⟆) .fst s
    Mod→PMod .fst s .F-hom f = (M ⟪ f ⟫) .fst s
    Mod→PMod .fst s .F-id = cong (λ h → h .fst s) (M .F-id)
    Mod→PMod .fst s .F-seq f g = cong (λ h → h .fst s) (M .F-seq f g)
    Mod→PMod .snd .PshAlgˢ.alg c = (M ⟅ c ⟆) .snd .fst
    Mod→PMod .snd .PshAlgˢ.sat c = (M ⟅ c ⟆) .snd .snd
    Mod→PMod .snd .PshAlgˢ.restr f = (M ⟪ f ⟫) .snd .fst

  module _ (N : Category.ob (PMOD ℓX)) where
    open Functor
    private
      isSetN : (c : C .ob) (s : S) → isSet ⟨ N .fst s ⟅ c ⟆ ⟩
      isSetN c s = str (N .fst s ⟅ c ⟆)

    PMod→Mod : Functor (C ^op) (MOD σeq ℓX)
    PMod→Mod .F-ob c =
      (λ s → N .fst s ⟅ c ⟆) , N .snd .PshAlgˢ.alg c , N .snd .PshAlgˢ.sat c
    PMod→Mod .F-hom f =
      (λ s → N .fst s ⟪ f ⟫) , N .snd .PshAlgˢ.restr f , tt*
    PMod→Mod .F-id =
      Σ≡Prop (λ _ → isPropΣ (isPropΠ4 (λ _ _ _ _ → isSetN _ _ _ _))
                            (λ _ → isPropUnit*))
        (funExt (λ s → N .fst s .F-id))
    PMod→Mod .F-seq f g =
      Σ≡Prop (λ _ → isPropΣ (isPropΠ4 (λ _ _ _ _ → isSetN _ _ _ _))
                            (λ _ → isPropUnit*))
        (funExt (λ s → N .fst s .F-seq f g))

  -- ... and the two directions are mutually inverse.  Neither round
  -- trip moves any data: `F-ob`/`F-hom` and `alg`/`sat`/`restr` all
  -- come back on the nose, and only the propositional functor laws
  -- have to be transported.
  PModIsoMod : Iso (Category.ob (PMOD ℓX)) (Functor (C ^op) (MOD σeq ℓX))
  PModIsoMod .Iso.fun = PMod→Mod
  PModIsoMod .Iso.inv = Mod→PMod
  PModIsoMod .Iso.sec M = Functor≡ (λ _ → refl) (λ _ → refl)
  PModIsoMod .Iso.ret N i .fst s =
    Functor≡ {F = Mod→PMod (PMod→Mod N) .fst s} {G = N .fst s}
      (λ _ → refl) (λ _ → refl) i
  PModIsoMod .Iso.ret N i .snd .PshAlgˢ.alg = N .snd .PshAlgˢ.alg
  PModIsoMod .Iso.ret N i .snd .PshAlgˢ.sat = N .snd .PshAlgˢ.sat
  PModIsoMod .Iso.ret N i .snd .PshAlgˢ.restr = N .snd .PshAlgˢ.restr
