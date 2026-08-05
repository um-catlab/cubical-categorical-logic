-- Combining sorted theories.
--
-- `_⊕Sig_`/`_⊕Eqns_` is the coproduct of two theories over the *same*
-- sort set: this is how a structural theory (a category, a CBPV) is
-- combined with an effect theory.
--
-- `atSig`/`atEqns` is the other half: it takes a single-sorted theory
-- and installs a copy of its operations *homogeneously* at each of a
-- chosen family of sorts.  For CBPV the chosen family is the oblique
-- hom sorts, and this is exactly what a `StateAlgEnrichment` is --
-- except that the naturality conditions become equations rather than
-- side conditions, which is the point.
module Cubical.Algebra.Theory.Sorted.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit

open import Cubical.Algebra.Theory.Sorted

private
  variable
    ℓS ℓ ℓ1 ℓ2 ℓ' ℓ'' ℓ1'' ℓ2'' ℓv ℓX ℓK : Level

open SortedSig
open SortedEqns

module _ {S : Type ℓS} (σ : SortedSig S ℓ1 ℓ') (τ : SortedSig S ℓ2 ℓ') where

  _⊕Sig_ : SortedSig S (ℓ-max ℓ1 ℓ2) ℓ'
  _⊕Sig_ .ops = σ .ops ⊎ τ .ops
  _⊕Sig_ .arities (inl o) = σ .arities o
  _⊕Sig_ .arities (inr o) = τ .arities o
  _⊕Sig_ .sortOf (inl o) = σ .sortOf o
  _⊕Sig_ .sortOf (inr o) = τ .sortOf o
  _⊕Sig_ .resultSort (inl o) = σ .resultSort o
  _⊕Sig_ .resultSort (inr o) = τ .resultSort o

  -- the two inclusions on terms; sorts are preserved on the nose, so
  -- there is no transport
  inlTm : {V : Type ℓv} {vs : V → S} {s : S}
    → Tm σ V vs s → Tm _⊕Sig_ V vs s
  inlTm (var v) = var v
  inlTm (node o ts) = node (inl o) (λ a → inlTm (ts a))

  inrTm : {V : Type ℓv} {vs : V → S} {s : S}
    → Tm τ V vs s → Tm _⊕Sig_ V vs s
  inrTm (var v) = var v
  inrTm (node o ts) = node (inr o) (λ a → inrTm (ts a))

  -- an interpretation of the sum restricts to each summand, definitionally
  resl : (X : S → Type ℓX) → Ops {σ = _⊕Sig_} X → Ops {σ = σ} X
  resl X α o = α (inl o)

  resr : (X : S → Type ℓX) → Ops {σ = _⊕Sig_} X → Ops {σ = τ} X
  resr X α o = α (inr o)

  TmRec-inl : (X : S → Type ℓX) (α : Ops {σ = _⊕Sig_} X)
    {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v))
    {s : S} (M : Tm σ V vs s)
    → TmRec X α ρ (inlTm M) ≡ TmRec X (resl X α) ρ M
  TmRec-inl X α ρ (var v) = refl
  TmRec-inl X α ρ (node o ts) =
    cong (α (inl o)) (funExt (λ a → TmRec-inl X α ρ (ts a)))

  TmRec-inr : (X : S → Type ℓX) (α : Ops {σ = _⊕Sig_} X)
    {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v))
    {s : S} (M : Tm τ V vs s)
    → TmRec X α ρ (inrTm M) ≡ TmRec X (resr X α) ρ M
  TmRec-inr X α ρ (var v) = refl
  TmRec-inr X α ρ (node o ts) =
    cong (α (inr o)) (funExt (λ a → TmRec-inr X α ρ (ts a)))

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ'} {τ : SortedSig S ℓ2 ℓ'}
  (σeq : SortedEqns σ ℓ1'' ℓv) (τeq : SortedEqns τ ℓ2'' ℓv) where

  _⊕Eqns_ : SortedEqns (σ ⊕Sig τ) (ℓ-max ℓ1'' ℓ2'') ℓv
  _⊕Eqns_ .eqns = σeq .eqns ⊎ τeq .eqns
  _⊕Eqns_ .eqnSort (inl e) = σeq .eqnSort e
  _⊕Eqns_ .eqnSort (inr e) = τeq .eqnSort e
  _⊕Eqns_ .vars (inl e) = σeq .vars e
  _⊕Eqns_ .vars (inr e) = τeq .vars e
  _⊕Eqns_ .varSort (inl e) = σeq .varSort e
  _⊕Eqns_ .varSort (inr e) = τeq .varSort e
  _⊕Eqns_ .lhs (inl e) = inlTm σ τ (σeq .lhs e)
  _⊕Eqns_ .lhs (inr e) = inrTm σ τ (τeq .lhs e)
  _⊕Eqns_ .rhs (inl e) = inlTm σ τ (σeq .rhs e)
  _⊕Eqns_ .rhs (inr e) = inrTm σ τ (τeq .rhs e)

  -- a model of the sum restricts to a model of each summand
  satl : (X : S → Type ℓX) (α : Ops {σ = σ ⊕Sig τ} X)
    → ((e : _⊕Eqns_ .eqns) (ρ : (v : _⊕Eqns_ .vars e) → X (_⊕Eqns_ .varSort e v))
       → TmRec X α ρ (_⊕Eqns_ .lhs e) ≡ TmRec X α ρ (_⊕Eqns_ .rhs e))
    → (e : σeq .eqns) (ρ : (v : σeq .vars e) → X (σeq .varSort e v))
    → TmRec X (resl σ τ X α) ρ (σeq .lhs e) ≡ TmRec X (resl σ τ X α) ρ (σeq .rhs e)
  satl X α sat e ρ =
    sym (TmRec-inl σ τ X α ρ (σeq .lhs e))
    ∙ sat (inl e) ρ
    ∙ TmRec-inl σ τ X α ρ (σeq .rhs e)

  satr : (X : S → Type ℓX) (α : Ops {σ = σ ⊕Sig τ} X)
    → ((e : _⊕Eqns_ .eqns) (ρ : (v : _⊕Eqns_ .vars e) → X (_⊕Eqns_ .varSort e v))
       → TmRec X α ρ (_⊕Eqns_ .lhs e) ≡ TmRec X α ρ (_⊕Eqns_ .rhs e))
    → (e : τeq .eqns) (ρ : (v : τeq .vars e) → X (τeq .varSort e v))
    → TmRec X (resr σ τ X α) ρ (τeq .lhs e) ≡ TmRec X (resr σ τ X α) ρ (τeq .rhs e)
  satr X α sat e ρ =
    sym (TmRec-inr σ τ X α ρ (τeq .lhs e))
    ∙ sat (inr e) ρ
    ∙ TmRec-inr σ τ X α ρ (τeq .rhs e)

-- Installing a single-sorted theory at a chosen family of sorts.  Every
-- argument and the result sit at the *same* sort `at k`, so the
-- operations act on one hom set at a time -- which is precisely what it
-- means for that hom set to carry an algebra.
module _ {S : Type ℓS} (K : Type ℓK) (at : K → S)
  (σ0 : SortedSig Unit ℓ ℓ') where

  atSig : SortedSig S (ℓ-max ℓ ℓK) ℓ'
  atSig .ops = σ0 .ops × K
  atSig .arities (o , k) = σ0 .arities o
  atSig .sortOf (o , k) a = at k
  atSig .resultSort (o , k) = at k

  atTm : (k : K) {V : Type ℓv}
    → Tm σ0 V (λ _ → tt) tt → Tm atSig V (λ _ → at k) (at k)
  atTm k (var v) = var v
  atTm k (node o ts) = node (o , k) (λ a → atTm k (ts a))

  atEqns : SortedEqns σ0 ℓ'' ℓv → SortedEqns atSig (ℓ-max ℓ'' ℓK) ℓv
  atEqns E .eqns = E .eqns × K
  atEqns E .eqnSort (e , k) = at k
  atEqns E .vars (e , k) = E .vars e
  atEqns E .varSort (e , k) v = at k
  atEqns E .lhs (e , k) = atTm k (E .lhs e)
  atEqns E .rhs (e , k) = atTm k (E .rhs e)

  -- An interpretation of `atSig` is exactly a `K`-indexed family of
  -- algebras for σ0, one on each `X (at k)`.
  atOps→Alg : (X : S → Type ℓX) → Ops {σ = atSig} X
    → (k : K) → Ops {σ = σ0} (λ _ → X (at k))
  atOps→Alg X α k o = α (o , k)

  Alg→atOps : (X : S → Type ℓX)
    → ((k : K) → Ops {σ = σ0} (λ _ → X (at k))) → Ops {σ = atSig} X
  Alg→atOps X β (o , k) = β k o

  atTmRec : (X : S → Type ℓX) (α : Ops {σ = atSig} X) (k : K)
    {V : Type ℓv} (ρ : V → X (at k)) (M : Tm σ0 V (λ _ → tt) tt)
    → TmRec X α ρ (atTm k M)
      ≡ TmRec (λ _ → X (at k)) (atOps→Alg X α k) ρ M
  atTmRec X α k ρ (var v) = refl
  atTmRec X α k ρ (node o ts) =
    cong (α (o , k)) (funExt (λ a → atTmRec X α k ρ (ts a)))

-- `_⊕Eqns_` only covers equations that mention one summand's operations.
-- The general situation -- U/F laws that mention composition, effect
-- operations that commute with composition -- needs equations stated
-- over the *sum* signature.  So: inject the pure ones, then union with
-- whatever else is wanted, all over one signature.
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ'} (τ : SortedSig S ℓ2 ℓ') where

  injEqnsL : SortedEqns σ ℓ'' ℓv → SortedEqns (σ ⊕Sig τ) ℓ'' ℓv
  injEqnsL E .eqns = E .eqns
  injEqnsL E .eqnSort = E .eqnSort
  injEqnsL E .vars = E .vars
  injEqnsL E .varSort = E .varSort
  injEqnsL E .lhs e = inlTm σ τ (E .lhs e)
  injEqnsL E .rhs e = inlTm σ τ (E .rhs e)

module _ {S : Type ℓS} (σ : SortedSig S ℓ1 ℓ') {τ : SortedSig S ℓ2 ℓ'} where

  injEqnsR : SortedEqns τ ℓ'' ℓv → SortedEqns (σ ⊕Sig τ) ℓ'' ℓv
  injEqnsR E .eqns = E .eqns
  injEqnsR E .eqnSort = E .eqnSort
  injEqnsR E .vars = E .vars
  injEqnsR E .varSort = E .varSort
  injEqnsR E .lhs e = inrTm σ τ (E .lhs e)
  injEqnsR E .rhs e = inrTm σ τ (E .rhs e)

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} where

  -- union of two sets of equations over the same signature
  _∪Eqns_ : SortedEqns σ ℓ1'' ℓv → SortedEqns σ ℓ2'' ℓv
    → SortedEqns σ (ℓ-max ℓ1'' ℓ2'') ℓv
  (E ∪Eqns E') .eqns = E .eqns ⊎ E' .eqns
  (E ∪Eqns E') .eqnSort (inl e) = E .eqnSort e
  (E ∪Eqns E') .eqnSort (inr e) = E' .eqnSort e
  (E ∪Eqns E') .vars (inl e) = E .vars e
  (E ∪Eqns E') .vars (inr e) = E' .vars e
  (E ∪Eqns E') .varSort (inl e) = E .varSort e
  (E ∪Eqns E') .varSort (inr e) = E' .varSort e
  (E ∪Eqns E') .lhs (inl e) = E .lhs e
  (E ∪Eqns E') .lhs (inr e) = E' .lhs e
  (E ∪Eqns E') .rhs (inl e) = E .rhs e
  (E ∪Eqns E') .rhs (inr e) = E' .rhs e
