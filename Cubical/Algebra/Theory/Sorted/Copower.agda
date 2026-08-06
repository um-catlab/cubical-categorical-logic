-- The `K`-fold copower of a single-sorted theory: `K` sorts, one
-- disjoint copy of the theory at each.  Nothing in the copower itself
-- mentions a target sort set; installing the copies somewhere is the
-- job of `reSig`, and that is what the second half of this file uses.
--
-- Validation of `ChangeOfSorts`: `atSig`/`atEqns` of
-- `Sorted.Constructions` -- installing a single-sorted theory
-- homogeneously at a chosen family `at : K → S` of sorts -- is exactly
-- relabelling applied to the copower.  On signatures the two agree on
-- the nose (`atSig≡` is `refl`); on equations they agree up to the
-- `reTm`/`⊗Tm` fusion, which is a pointwise `cong`.  So `atSig` is not
-- a separate construction, and `atOps→Alg` is the copower's currying
-- composed with the definitional equality
--
--     Ops {reSig σ} X  ≡  Ops {σ} (X ∘ h)
--
-- that drives `ChangeOfSorts`.  Running the models theorem through that
-- identification gives `atModAlg`: a model of the theory installed at
-- `at` is a `K`-indexed family of models of the single-sorted theory,
-- one on each `X (at k)`.  For CBPV that is the statement that each
-- oblique hom set carries an algebra, i.e. what a
-- `StateAlgEnrichment` asserts -- now a corollary rather than a
-- definition.
module Cubical.Algebra.Theory.Sorted.Copower where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base

open import Cubical.Algebra.Theory.Sorted
open import Cubical.Algebra.Theory.Sorted.Constructions
open import Cubical.Algebra.Theory.Sorted.ChangeOfSorts

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX ℓK : Level

open SortedSig
open SortedEqns

module _ (K : Type ℓK) (σ0 : SortedSig Unit ℓ ℓ') where

  ⊗Sig : SortedSig K (ℓ-max ℓ ℓK) ℓ'
  ⊗Sig .ops = σ0 .ops × K
  ⊗Sig .arities (o , k) = σ0 .arities o
  ⊗Sig .sortOf (o , k) a = k
  ⊗Sig .resultSort (o , k) = k

  ⊗Tm : (k : K) {V : Type ℓv}
    → Tm σ0 V (λ _ → tt) tt → Tm ⊗Sig V (λ _ → k) k
  ⊗Tm k (var v) = var v
  ⊗Tm k (node o ts) = node (o , k) (λ a → ⊗Tm k (ts a))

  ⊗Eqns : SortedEqns σ0 ℓ'' ℓv → SortedEqns ⊗Sig (ℓ-max ℓ'' ℓK) ℓv
  ⊗Eqns E .eqns = E .eqns × K
  ⊗Eqns E .eqnSort (e , k) = k
  ⊗Eqns E .vars (e , k) = E .vars e
  ⊗Eqns E .varSort (e , k) v = k
  ⊗Eqns E .lhs (e , k) = ⊗Tm k (E .lhs e)
  ⊗Eqns E .rhs (e , k) = ⊗Tm k (E .rhs e)

  -- an interpretation of the copower is a `K`-indexed family of
  -- interpretations of the original, by currying alone
  ⊗Ops : (X : K → Type ℓX)
    → Iso (Ops {σ = ⊗Sig} X) ((k : K) → Ops {σ = σ0} (λ _ → X k))
  ⊗Ops X .Iso.fun α k o = α (o , k)
  ⊗Ops X .Iso.inv β (o , k) = β k o
  ⊗Ops X .Iso.sec β = refl
  ⊗Ops X .Iso.ret α = refl

  ⊗TmRec : (X : K → Type ℓX) (α : Ops {σ = ⊗Sig} X) (k : K)
    {V : Type ℓv} (ρ : V → X k) (M : Tm σ0 V (λ _ → tt) tt)
    → TmRec X α ρ (⊗Tm k M)
      ≡ TmRec (λ _ → X k) (⊗Ops X .Iso.fun α k) ρ M
  ⊗TmRec X α k ρ (var v) = refl
  ⊗TmRec X α k ρ (node o ts) =
    cong (α (o , k)) (funExt (λ a → ⊗TmRec X α k ρ (ts a)))

  -- and a model of the copower is a `K`-indexed family of models
  ⊗ModOb : (E : SortedEqns σ0 ℓ'' ℓv) (ℓX : Level)
    (Y : Category.ob (FAM K ℓX))
    → Iso (Categoryᴰ.ob[_] (MODᴰ (⊗Eqns E) ℓX) Y)
          ((k : K) → Categoryᴰ.ob[_] (MODᴰ E ℓX) (λ _ → Y k))
  ⊗ModOb E ℓX Y .Iso.fun αs k .fst = ⊗Ops (λ k₀ → ⟨ Y k₀ ⟩) .Iso.fun (αs .fst) k
  ⊗ModOb E ℓX Y .Iso.fun αs k .snd e ρ =
    sym (⊗TmRec _ (αs .fst) k ρ (E .lhs e))
    ∙ αs .snd (e , k) ρ
    ∙ ⊗TmRec _ (αs .fst) k ρ (E .rhs e)
  ⊗ModOb E ℓX Y .Iso.inv βs .fst =
    ⊗Ops (λ k₀ → ⟨ Y k₀ ⟩) .Iso.inv (λ k → βs k .fst)
  ⊗ModOb E ℓX Y .Iso.inv βs .snd (e , k) ρ =
    ⊗TmRec _ (⊗Ops (λ k₀ → ⟨ Y k₀ ⟩) .Iso.inv (λ k₀ → βs k₀ .fst)) k ρ
      (E .lhs e)
    ∙ βs k .snd e ρ
    ∙ sym (⊗TmRec _ (⊗Ops (λ k₀ → ⟨ Y k₀ ⟩) .Iso.inv (λ k₀ → βs k₀ .fst))
             k ρ (E .rhs e))
  ⊗ModOb E ℓX Y .Iso.sec βs =
    funExt (λ k →
      Σ≡Prop (λ _ → isPropΠ2 (λ _ _ → Y k .snd _ _)) refl)
  ⊗ModOb E ℓX Y .Iso.ret αs =
    Σ≡Prop (λ _ → isPropΠ2 (λ ek _ → Y (ek .snd) .snd _ _)) refl

-- `atSig`/`atEqns` recovered: install the copower at `at`.
module _ {S : Type ℓS} (K : Type ℓK) (at : K → S)
  (σ0 : SortedSig Unit ℓ ℓ') where

  atSig≡ : atSig K at σ0 ≡ reSig at (⊗Sig K σ0)
  atSig≡ = refl

  atTm≡ : (k : K) {V : Type ℓv} (M : Tm σ0 V (λ _ → tt) tt)
    → atTm K at σ0 k M ≡ reTm at (⊗Tm K σ0 k M)
  atTm≡ k (var v) = refl
  atTm≡ k (node o ts) =
    cong (node (o , k)) (funExt (λ a → atTm≡ k (ts a)))

  atEqns≡ : (E : SortedEqns σ0 ℓ'' ℓv)
    → atEqns K at σ0 E ≡ reEqns at (⊗Eqns K σ0 E)
  atEqns≡ E i .eqns = E .eqns × K
  atEqns≡ E i .eqnSort (e , k) = at k
  atEqns≡ E i .vars (e , k) = E .vars e
  atEqns≡ E i .varSort (e , k) v = at k
  atEqns≡ E i .lhs (e , k) = atTm≡ k (E .lhs e) i
  atEqns≡ E i .rhs (e , k) = atTm≡ k (E .rhs e) i

  -- and `atOps→Alg` is the copower's currying, read through the
  -- definitional equality `reOps`
  atOps : (X : S → Type ℓX)
    → Iso (Ops {σ = atSig K at σ0} X)
          ((k : K) → Ops {σ = σ0} (λ _ → X (at k)))
  atOps X = ⊗Ops K σ0 (λ k → X (at k))

  atOps≡ : (X : S → Type ℓX)
    → atOps X .Iso.fun ≡ atOps→Alg K at σ0 X
  atOps≡ X = refl

  -- The models theorem, transported to `atEqns`: a model of the theory
  -- installed at `at` is a `K`-indexed family of models of the
  -- single-sorted theory, one on each chosen carrier `X (at k)`.  This
  -- is the statement `atSig` was built to make -- for CBPV, that the
  -- oblique hom sets carry an algebra -- and it is now a corollary of
  -- change of sorts rather than a construction of its own.
  atModOb : (E : SortedEqns σ0 ℓ'' ℓv) (ℓX : Level)
    (X : Category.ob (FAM S ℓX))
    → Iso (Categoryᴰ.ob[_] (MODᴰ (atEqns K at σ0 E) ℓX) X)
          (Categoryᴰ.ob[_] (MODᴰ (⊗Eqns K σ0 E) ℓX) (λ k → X (at k)))
  atModOb E ℓX X =
    subst
      (λ F → Iso (Categoryᴰ.ob[_] (MODᴰ F ℓX) X)
                 (Categoryᴰ.ob[_] (MODᴰ (⊗Eqns K σ0 E) ℓX)
                   (λ k → X (at k))))
      (sym (atEqns≡ E))
      (reModOb at (⊗Eqns K σ0 E) ℓX X)

  atModAlg : (E : SortedEqns σ0 ℓ'' ℓv) (ℓX : Level)
    (X : Category.ob (FAM S ℓX))
    → Iso (Categoryᴰ.ob[_] (MODᴰ (atEqns K at σ0 E) ℓX) X)
          ((k : K) → Categoryᴰ.ob[_] (MODᴰ E ℓX) (λ _ → X (at k)))
  atModAlg E ℓX X =
    compIso (atModOb E ℓX X) (⊗ModOb K σ0 E ℓX (λ k → X (at k)))
