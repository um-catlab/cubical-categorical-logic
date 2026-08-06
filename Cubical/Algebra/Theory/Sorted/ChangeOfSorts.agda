{-# OPTIONS --lossy-unification #-}
-- Change of sorts: transporting a sorted theory along a map of sort
-- sets `h : S → S'`.
--
-- On *syntax* this is a pushforward.  A signature is a set of operations
-- together with `sortOf`/`resultSort` naming where each argument and the
-- result live; relabelling is postcomposition with `h` on those two
-- fields and nothing else, so `Tm` transports by renaming a term to
-- itself.  No path between sorts is ever formed -- which is the whole
-- reason `SortedSig` carries `sortOf : (o : ops) → arities o → S` rather
-- than fibring `arities` over `S`.
--
-- On *models* it is a pullback.  `h` induces `ΔFam : FAM S' → FAM S` by
-- precomposition, and the point of the construction is that
--
--     Ops {reSig σ} X  ≡  Ops {σ} (X ∘ h)                 (definitionally)
--
-- so a model of the relabelled theory is exactly an `S'`-family whose
-- reindexing along `h` is a model of the original.  The theorem below
-- says this at the level of categories: the square
--
--     MOD (reEqns E) ----→ MOD E
--          |                 |
--          ↓                 ↓
--       FAM S'  --ΔFam-→   FAM S
--
-- is a pullback, i.e. `MODᴰ (reEqns E)` is the reindexing of `MODᴰ E`
-- along `ΔFam`.  It is proved by exhibiting the comparison as a
-- `Functorᴰ` whose action on displayed objects and on displayed
-- morphisms are both equivalences; on morphisms it is literally the
-- identity function, and on objects it is the identity on the algebra
-- structure and a propositional adjustment on the equations, since the
-- two sides of an equation are relabelled terms.
--
-- What does NOT work, and why.  `ΔFam` has adjoints on families
-- (`Σ_h`, `Π_h` along `h`), but neither lifts to theories.  For `Π_h` one
-- would need, from a signature on `S'`, a signature on `S`: that means
-- choosing for every operation an `S`-lift of its result sort and of
-- each of its argument sorts, i.e. an element of
-- `fiber h s' = Σ[ s ∈ S ] h s ≡ s'`.  The chosen lift then has to be
-- compared with the sort an argument actually sits at, and the
-- comparison is the path component of the fibre -- a `subst` at every
-- occurrence of every operation, which is precisely the fibred
-- presentation this file's header disclaims.  The one case where it is
-- path-free is when `h` is presented as a display map, `fst : Σ S' B →
-- S'`, whose fibre over `s'` is `B s'` on the nose; but then the
-- resulting theory's models are σ'-structures parameterised by all
-- choices of `B`-indices, which is neither `Σ_h` nor `Π_h` of a
-- σ'-model, so the construction has no models theorem and is omitted.
-- For `Σ_h` the failure is earlier: an operation of the pushed-forward
-- theory would have to act on `Σ_h X` at arbitrary tuples of fibres,
-- while the original supplies operations one fibre at a time.
--
-- Relation to `Sorted.Over`.  There a displayed sort is indexed by a
-- base *term* rather than by an element of a fixed set, and `SigAt`
-- produces a signature on `SortAt = Σ[ i ∈ Shape ] X (base i)`.  That is
-- the dependent version of the same move: the map of sort sets is
-- replaced by a family, and the operations acquire an environment
-- argument, so `SigAt` is not `reSig` of anything.  `reSig` is the
-- special case in which the family is constant, and it is exactly the
-- part that needs no fording: `Over`'s `OpAt` fords the result index
-- because two index *terms* agree only in every model, whereas here the
-- relabelled sorts agree by computation.
module Cubical.Algebra.Theory.Sorted.ChangeOfSorts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Instances.TotalCategory

open import Cubical.Algebra.Theory.Sorted
open import Cubical.Algebra.Theory.Sorted.Constructions

private
  variable
    ℓS ℓS' ℓS'' ℓ ℓ' ℓ'' ℓv ℓX ℓK : Level

open SortedSig
open SortedEqns
open Functor
open Functorᴰ

-- Relabelling a theory along a map of sort sets.
module _ {S : Type ℓS} {S' : Type ℓS'} (h : S → S') where

  reSig : SortedSig S ℓ ℓ' → SortedSig S' ℓ ℓ'
  reSig σ .ops = σ .ops
  reSig σ .arities = σ .arities
  reSig σ .sortOf o a = h (σ .sortOf o a)
  reSig σ .resultSort o = h (σ .resultSort o)

  module _ {σ : SortedSig S ℓ ℓ'} where

    -- renaming a term to itself: every sort in sight is relabelled by
    -- `h`, so there is nothing to transport
    reTm : {V : Type ℓv} {vs : V → S} {s : S}
      → Tm σ V vs s → Tm (reSig σ) V (λ v → h (vs v)) (h s)
    reTm (var v) = var v
    reTm (node o ts) = node o (λ a → reTm (ts a))

    -- the whole point: interpreting the relabelled signature in an
    -- `S'`-family *is* interpreting the original in its reindexing
    reOps : (X : S' → Type ℓX)
      → Ops {σ = reSig σ} X ≡ Ops {σ = σ} (λ s → X (h s))
    reOps X = refl

    TmRec-reTm : (X : S' → Type ℓX) (α : Ops {σ = reSig σ} X)
      {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (h (vs v)))
      {s : S} (M : Tm σ V vs s)
      → TmRec X α ρ (reTm M) ≡ TmRec (λ s₀ → X (h s₀)) α ρ M
    TmRec-reTm X α ρ (var v) = refl
    TmRec-reTm X α ρ (node o ts) =
      cong (α o) (funExt (λ a → TmRec-reTm X α ρ (ts a)))

  reEqns : {σ : SortedSig S ℓ ℓ'}
    → SortedEqns σ ℓ'' ℓv → SortedEqns (reSig σ) ℓ'' ℓv
  reEqns E .eqns = E .eqns
  reEqns E .eqnSort e = h (E .eqnSort e)
  reEqns E .vars = E .vars
  reEqns E .varSort e v = h (E .varSort e v)
  reEqns E .lhs e = reTm (E .lhs e)
  reEqns E .rhs e = reTm (E .rhs e)

  -- the reindexing of families, on the nose
  ΔFam : (ℓX : Level) → Functor (FAM S' ℓX) (FAM S ℓX)
  ΔFam ℓX .F-ob X s = X (h s)
  ΔFam ℓX .F-hom f s = f (h s)
  ΔFam ℓX .F-id = refl
  ΔFam ℓX .F-seq f g = refl

-- The models theorem.
module _ {S : Type ℓS} {S' : Type ℓS'} (h : S → S')
  {σ : SortedSig S ℓ ℓ'} (E : SortedEqns σ ℓ'' ℓv) (ℓX : Level) where

  private
    module Mre = Categoryᴰ (MODᴰ (reEqns h E) ℓX)
    module M = Categoryᴰ (MODᴰ E ℓX)

    Δ : Functor (FAM S' ℓX) (FAM S ℓX)
    Δ = ΔFam h ℓX

  -- A model of the relabelled theory over `X` is a model of the original
  -- over `X ∘ h`.  The algebra structure is untouched; only the
  -- equations, whose sides are relabelled terms, need the fusion lemma,
  -- and satisfaction is a proposition, so this is an `Iso`.
  reModOb : (X : Category.ob (FAM S' ℓX))
    → Iso Mre.ob[ X ] M.ob[ Δ .F-ob X ]
  reModOb X .Iso.fun αs .fst = αs .fst
  reModOb X .Iso.fun αs .snd e ρ =
    sym (TmRec-reTm h _ (αs .fst) ρ (E .lhs e))
    ∙ αs .snd e ρ
    ∙ TmRec-reTm h _ (αs .fst) ρ (E .rhs e)
  reModOb X .Iso.inv αs .fst = αs .fst
  reModOb X .Iso.inv αs .snd e ρ =
    TmRec-reTm h _ (αs .fst) ρ (E .lhs e)
    ∙ αs .snd e ρ
    ∙ sym (TmRec-reTm h _ (αs .fst) ρ (E .rhs e))
  reModOb X .Iso.sec αs =
    Σ≡Prop
      (λ _ → isPropΠ2 (λ e _ → X (h (E .eqnSort e)) .snd _ _))
      refl
  reModOb X .Iso.ret αs =
    Σ≡Prop
      (λ _ → isPropΠ2 (λ e _ → X (h (E .eqnSort e)) .snd _ _))
      refl

  -- On morphisms there is nothing to do at all: the forded homomorphism
  -- condition for `reSig σ` at `f` and the one for `σ` at `f ∘ h` are
  -- the same type.
  reModHom : {X Y : Category.ob (FAM S' ℓX)}
    (f : Category.Hom[_,_] (FAM S' ℓX) X Y)
    (Mᴰ : Mre.ob[ X ]) (Nᴰ : Mre.ob[ Y ])
    → Iso (Mre.Hom[ f ][ Mᴰ , Nᴰ ])
          (M.Hom[ Δ .F-hom f ][ reModOb X .Iso.fun Mᴰ
                              , reModOb Y .Iso.fun Nᴰ ])
  reModHom f Mᴰ Nᴰ = idIso

  -- The comparison functor over `ΔFam`.
  reModᴰ : Functorᴰ Δ (MODᴰ (reEqns h E) ℓX) (MODᴰ E ℓX)
  reModᴰ .F-obᴰ {x = X} = reModOb X .Iso.fun
  reModᴰ .F-homᴰ fᴰ = fᴰ
  reModᴰ .F-idᴰ = refl
  reModᴰ .F-seqᴰ fᴰ gᴰ = refl

  reMod : Functor (MOD (reEqns h E) ℓX) (MOD E ℓX)
  reMod = ∫F reModᴰ

  -- ... and it is an isomorphism of displayed categories, i.e. the
  -- square is a pullback.
  isEquivReModObᴰ : (X : Category.ob (FAM S' ℓX))
    → isEquiv (reModᴰ .F-obᴰ {x = X})
  isEquivReModObᴰ X = isoToIsEquiv (reModOb X)

  isEquivReModHomᴰ : {X Y : Category.ob (FAM S' ℓX)}
    {f : Category.Hom[_,_] (FAM S' ℓX) X Y}
    {Mᴰ : Mre.ob[ X ]} {Nᴰ : Mre.ob[ Y ]}
    → isEquiv (reModᴰ .F-homᴰ {f = f} {xᴰ = Mᴰ} {yᴰ = Nᴰ})
  isEquivReModHomᴰ = idIsEquiv _

  -- the induced statement about total categories
  reModObTotal : Iso (Category.ob (MOD (reEqns h E) ℓX))
    (Σ[ X ∈ Category.ob (FAM S' ℓX) ] M.ob[ Δ .F-ob X ])
  reModObTotal = Σ-cong-iso-snd reModOb

-- Relabelling is a strict action: it is functorial in `h` on the nose
-- on signatures, and up to `reTm` fusion on equations.
module _ {S : Type ℓS} (σ : SortedSig S ℓ ℓ') where

  reSigId : reSig (idfun S) σ ≡ σ
  reSigId = refl

module _ {S : Type ℓS} {S' : Type ℓS'} {S'' : Type ℓS''}
  (h : S → S') (g : S' → S'') where

  reSigComp : (σ : SortedSig S ℓ ℓ')
    → reSig g (reSig h σ) ≡ reSig (λ s → g (h s)) σ
  reSigComp σ = refl

  module _ {σ : SortedSig S ℓ ℓ'} where

    reTmComp : {V : Type ℓv} {vs : V → S} {s : S} (M : Tm σ V vs s)
      → reTm g (reTm h M) ≡ reTm (λ s₀ → g (h s₀)) M
    reTmComp (var v) = refl
    reTmComp (node o ts) =
      cong (node o) (funExt (λ a → reTmComp (ts a)))

  reEqnsComp : {σ : SortedSig S ℓ ℓ'} (E : SortedEqns σ ℓ'' ℓv)
    → reEqns g (reEqns h E) ≡ reEqns (λ s → g (h s)) E
  reEqnsComp E i .eqns = E .eqns
  reEqnsComp E i .eqnSort e = g (h (E .eqnSort e))
  reEqnsComp E i .vars = E .vars
  reEqnsComp E i .varSort e v = g (h (E .varSort e v))
  reEqnsComp E i .lhs e = reTmComp (E .lhs e) i
  reEqnsComp E i .rhs e = reTmComp (E .rhs e) i
