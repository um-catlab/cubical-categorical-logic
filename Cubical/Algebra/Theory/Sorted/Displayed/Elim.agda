module Cubical.Algebra.Theory.Sorted.Displayed.Elim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category

open import Cubical.Algebra.Theory.Sorted
  using (SortedSig; SortedEqns; Ops; MOD; ModHom)
open import Cubical.Algebra.Theory.Sorted.Free.Closing
  using (FreeModel; FreeOps; FreeOb; gen; UPMod; ℓClosing)
open import Cubical.Algebra.Theory.Sorted.Displayed.Base

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓSᴰ ℓi : Level

open SortedSig
open SortedEqns
open SortedSigᴰ
open Sectionᴰ
open Modelᴰˢ

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  (V : Type ℓv) (vs : V → S) (σᴰ : SortedSigᴰ σ ℓSᴰ ℓi) where

  private
    ℓC = ℓClosing ℓS ℓ ℓ' ℓ'' ℓv

    F : Category.ob (MOD σeq ℓC)
    F = FreeOb σeq V vs

  module _ (Mᴰ : Modelᴰˢ σeq F σᴰ ℓC) (sec : Sectionᴰ σᴰ) where

    Fibᴰ : (s : S) → σᴰ .Sortᴰ s → FreeModel σeq V vs s → Type ℓC
    Fibᴰ s sᴰ x = ⟨ Mᴰ .carrierᴰ s sᴰ x ⟩

    module _ (ρᴰ : (v : V)
                 → Fibᴰ (vs v) (sec .secSort (vs v)) (gen σeq V vs v))
      where

      private
        N : Category.ob (MOD σeq ℓC)
        N = ∫Mod σeq F σᴰ Mᴰ sec

        rel : ModHom σeq ℓC F N
        rel = Iso.inv (UPMod σeq V vs N) (λ v → gen σeq V vs v , ρᴰ v)

        relπ : ModHom σeq ℓC F F
        relπ = Category._⋆_ (MOD σeq ℓC) {x = F} {y = N} {z = F}
                 rel (∫π σeq F σᴰ Mᴰ sec)

        splits : relπ ≡ Category.id (MOD σeq ℓC) {x = F}
        splits = isoFunInjective (UPMod σeq V vs F) relπ
                   (Category.id (MOD σeq ℓC) {x = F}) refl

        base : (s : S) (x : FreeModel σeq V vs s) → rel .fst s x .fst ≡ x
        base s x = funExt⁻ (funExt⁻ (cong fst splits) s) x

      splitting : Splitting σeq F σᴰ Mᴰ sec
      splitting = rel , splits

      elim : (s : S) (x : FreeModel σeq V vs s)
        → Fibᴰ s (sec .secSort s) x
      elim s x =
        subst (Fibᴰ s (sec .secSort s)) (base s x) (rel .fst s x .snd)

      elimβ : (v : V) → elim (vs v) (gen σeq V vs v) ≡ ρᴰ v
      elimβ v =
        cong (λ p → subst (Fibᴰ (vs v) (sec .secSort (vs v))) p (ρᴰ v))
          (F .fst (vs v) .snd (gen σeq V vs v) (gen σeq V vs v)
            (base (vs v) (gen σeq V vs v)) refl)
        ∙ substRefl {B = Fibᴰ (vs v) (sec .secSort (vs v))} (ρᴰ v)

  module _ (sec : Sectionᴰ σᴰ)
    (P : (s : S) → σᴰ .Sortᴰ s → FreeModel σeq V vs s → Type ℓC)
    (isPropP : (s : S) (sᴰ : σᴰ .Sortᴰ s) (x : FreeModel σeq V vs s)
             → isProp (P s sᴰ x))
    (Pop : (o : σ .ops) (i : σᴰ .opIdxᴰ o)
           (x : (a : σ .arities o) → FreeModel σeq V vs (σ .sortOf o a))
         → ((a : σ .arities o)
            → P (σ .sortOf o a) (σᴰ .argSortᴰ o i a) (x a))
         → P (σ .resultSort o) (σᴰ .resSortᴰ o i) (FreeOps σeq o x))
    (Pgen : (v : V)
          → P (vs v) (sec .secSort (vs v)) (gen σeq V vs v))
    where

    private
      Pᴰ : Modelᴰˢ σeq F σᴰ ℓC
      Pᴰ .carrierᴰ s sᴰ x = P s sᴰ x , isProp→isSet (isPropP s sᴰ x)
      Pᴰ .opsᴰ o i x xᴰ y eq =
        subst (P (σ .resultSort o) (σᴰ .resSortᴰ o i)) (sym eq)
          (Pop o i x xᴰ)
      Pᴰ .satᴰ e vsᴰ sᴰ L R ρ ρᴰ =
        isProp→PathP (λ _ → isPropP _ _ _) _ _

    elimProp : (s : S) (x : FreeModel σeq V vs s)
      → P s (sec .secSort s) x
    elimProp = elim Pᴰ sec Pgen
