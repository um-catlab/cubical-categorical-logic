-- Free models, functorially in the theory, for arbitrary theories
module Cubical.Algebra.Theory.Free.Section where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Limits.Initial

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Category
open import Cubical.Algebra.Theory.Theories
open import Cubical.Algebra.Theory.Free.Explicit

private
  variable
    ℓ ℓ'' ℓv ℓX : Level

ℓFree : (ℓ ℓ'' ℓv : Level) → Level
ℓFree ℓ ℓ'' ℓv = ℓ-max (ℓ-max ℓ ℓv) (ℓ-max ℓ'' (ℓ-suc ℓv))

module _ {σ : AlgTheorySig ℓ ℓv} (σeq : AlgTheoryEqns σ ℓ'' ℓv) where
  private
    ℓF = ℓFree ℓ ℓ'' ℓv

  FreeOb : (V : Type ℓv) → Category.ob (MOD σeq ℓF)
  FreeOb V = (FreeModel σeq V , trunc) , FreeAlg σeq V

  gen : (V : Type ℓv) → V → FreeModel σeq V
  gen V = var

  UPMod : (V : Type ℓv) (N : Category.ob (MOD σeq ℓF))
    → Iso (ModHom σeq ℓF (FreeOb V) N) (V → ⟨ N .fst ⟩)
  UPMod V N .Iso.fun (f , _) v = f (gen V v)
  UPMod V N .Iso.inv ρ =
    rec σeq (N .fst .snd) (N .snd) ρ
    , recHomo σeq (N .fst .snd) (N .snd) ρ
  UPMod V N .Iso.sec ρ = refl
  UPMod V N .Iso.ret (f , ϕ) =
    Σ≡Prop (λ _ → isPropHomo σeq (N .fst .snd))
      (funExt (λ x →
        sym (recUniq σeq (N .fst .snd) (N .snd) _ f ϕ (λ _ → refl) x)))

  -- `FreeOb V` is free on V, i.e. initial in the coslice V ↓ Forget --
  -- that is what `UPMod` says.  Initiality in MOD itself is the case of
  -- no generators.
  isInitialFreeOb : isInitial (MOD σeq ℓF) (FreeOb (⊥* {ℓv}))
  isInitialFreeOb N =
    isOfHLevelRetractFromIso 0 (UPMod (⊥* {ℓv}) N)
      ((λ ()) , (λ f → funExt (λ ())))

  InitialMOD : Initial (MOD σeq ℓF)
  InitialMOD = FreeOb (⊥* {ℓv}) , isInitialFreeOb

module _ (ℓ ℓ'' ℓv : Level) where
  private
    ℓF = ℓFree ℓ ℓ'' ℓv

  TH : Category _ _
  TH = THEORY ℓ ℓv ℓ'' ℓv ℓF

  thy : (T : Category.ob TH) → AlgTheoryEqns (SetSig.sig (T .fst)) ℓ'' ℓv
  thy T = T .snd

  module _ {T U : Category.ob TH} (h : Category.Hom[_,_] TH T U) where
    ReindexMod : Functor (MOD (thy U) ℓF) (MOD (thy T) ℓF)
    ReindexMod = ∫F (MODReindexᴰ (h .snd))

    ForgetReindexMod :
      funcComp (Forget (thy T)) ReindexMod ≡ Forget (thy U)
    ForgetReindexMod = Functor≡ (λ _ → refl) (λ _ → refl)

  MODOVERᴰ : Categoryᴰ TH _ _
  MODOVERᴰ .Categoryᴰ.ob[_] T = Category.ob (MOD (thy T) ℓF)
  MODOVERᴰ .Categoryᴰ.Hom[_][_,_] {x = T} {y = U} h M N =
    ModHom (thy T) ℓF M
      (Functor.F-ob (ReindexMod {T = T} {U = U} h) N)
  MODOVERᴰ .Categoryᴰ.idᴰ {x = T} {p = M} =
    Category.id (MOD (thy T) ℓF) {x = M}
  MODOVERᴰ .Categoryᴰ._⋆ᴰ_ {x = T} {y = U} {z = W} {f = h} {g = k}
    {xᴰ = M} {yᴰ = N} {zᴰ = P} ϕ ψ =
    Category._⋆_ (MOD (thy T) ℓF)
      {x = M} {y = Functor.F-ob (ReindexMod {T = T} {U = U} h) N}
      {z = Functor.F-ob (ReindexMod {T = T} {U = U} h)
             (Functor.F-ob (ReindexMod {T = U} {U = W} k) P)}
      ϕ (Functor.F-hom (ReindexMod {T = T} {U = U} h) ψ)
  MODOVERᴰ .Categoryᴰ.⋆IdLᴰ ϕ = refl
  MODOVERᴰ .Categoryᴰ.⋆IdRᴰ ϕ = refl
  MODOVERᴰ .Categoryᴰ.⋆Assocᴰ ϕ ψ χ = refl
  MODOVERᴰ .Categoryᴰ.isSetHomᴰ {x = T} {y = U} {f = h} {xᴰ = M} {yᴰ = N} =
    Category.isSetHom (MOD (thy T) ℓF)
      {x = M} {y = Functor.F-ob (ReindexMod {T = T} {U = U} h) N}

  module _ (V : Type ℓv) where
    private
      reOb : (T U : Category.ob TH) (h : Category.Hom[_,_] TH T U)
        → Category.ob (MOD (thy U) ℓF) → Category.ob (MOD (thy T) ℓF)
      reOb T U h = Functor.F-ob (ReindexMod {T = T} {U = U} h)

    FreeSection : GlobalSection MODOVERᴰ
    FreeSection .Section.F-obᴰ T = FreeOb (thy T) V
    FreeSection .Section.F-homᴰ {T} {U} h =
      Iso.inv (UPMod (thy T) V (reOb T U h (FreeOb (thy U) V)))
        (gen (thy U) V)
    FreeSection .Section.F-idᴰ {T} =
      isoFunInjective (UPMod (thy T) V (FreeOb (thy T) V)) _ _ refl
    FreeSection .Section.F-seqᴰ {T} {U} {W} h k =
      isoFunInjective
        (UPMod (thy T) V
          (reOb T W (Category._⋆_ TH {x = T} {y = U} {z = W} h k)
            (FreeOb (thy W) V))) _ _ refl
