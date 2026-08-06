{-# OPTIONS --lossy-unification #-}
-- Free models of a many-sorted theory, functorially in the theory.
--
-- This is the sorted analogue of `Theory.Free.Section`: the headline
-- is `FreeSection : GlobalSection MODOVERᴰ`, the free-model
-- construction presented as a global section of the category of
-- models displayed over the category of theories, i.e. natural in the
-- theory rather than constructed anew for each fixed theory.
module Cubical.Algebra.Theory.Sorted.Section where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Limits.Initial

open import Cubical.Algebra.Theory.Sorted
import Cubical.Algebra.Theory.Sorted.Morphism as Mor

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX : Level
    ℓ1 ℓ1' ℓ2 ℓ2' ℓ3 ℓ3' : Level

open SortedSig
open SortedEqns

-- ------------------------------------------------------------------
-- LOCAL SCAFFOLDING: the category of sorted theories.
--
-- This block exists only because `Theory.Sorted.Theories` was not
-- available when this file was written; it should later be replaced
-- by that shared development.  Everything below the marker
-- "END LOCAL SCAFFOLDING" is the actual content of this module.
--
-- The one design decision worth transplanting: a signature map stores
-- the sort *coercions* as data, not the sort *equations*.  Storing
--
--     onResult : (o : σ .ops) → σ .resultSort o Eq.≡ τ .resultSort (F o)
--
-- makes composition chain with `Eq._∙_`, and `p Eq.∙ Eq.refl` does not
-- reduce, so only `⋆IdL` is `refl`.  Worse, restriction of models is
-- then only *pseudo*functorial: `Eq.transport X (Eq.sym (p Eq.∙ q))` is
-- not `Eq.transport X (Eq.sym p) ∘ Eq.transport X (Eq.sym q)`.  Storing
-- the coercions themselves -- together with their naturality in the
-- forded "consume a proof, produce a proof" form -- makes composition
-- literally function composition, hence `refl`-associative and
-- `refl`-unital, and makes `resOps` strictly functorial.  Every honest
-- signature map gives one of these: see `fromSortedSigMap`.
-- ------------------------------------------------------------------

record SigMapᶠ {S : Type ℓS} (ℓX : Level)
  (σ : SortedSig S ℓ1 ℓ1') (τ : SortedSig S ℓ2 ℓ2')
  : Type (ℓ-max (ℓ-max ℓS (ℓ-suc ℓX))
          (ℓ-max (ℓ-max ℓ1 ℓ2) (ℓ-max ℓ1' ℓ2'))) where
  field
    onOps : σ .ops → τ .ops
    unArity : (o : σ .ops) → τ .arities (onOps o) → σ .arities o
    coeArg : (X : S → hSet ℓX) (o : σ .ops) (a : τ .arities (onOps o))
      → ⟨ X (σ .sortOf o (unArity o a)) ⟩ → ⟨ X (τ .sortOf (onOps o) a) ⟩
    coeRes : (X : S → hSet ℓX) (o : σ .ops)
      → ⟨ X (τ .resultSort (onOps o)) ⟩ → ⟨ X (σ .resultSort o) ⟩
    natArg : (X Y : S → hSet ℓX) (g : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
      (o : σ .ops) (a : τ .arities (onOps o))
      (z : ⟨ X (σ .sortOf o (unArity o a)) ⟩)
      (w : ⟨ Y (σ .sortOf o (unArity o a)) ⟩)
      → g (σ .sortOf o (unArity o a)) z ≡ w
      → g (τ .sortOf (onOps o) a) (coeArg X o a z) ≡ coeArg Y o a w
    natRes : (X Y : S → hSet ℓX) (g : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
      (o : σ .ops)
      (z : ⟨ X (τ .resultSort (onOps o)) ⟩)
      (w : ⟨ Y (τ .resultSort (onOps o)) ⟩)
      → g (τ .resultSort (onOps o)) z ≡ w
      → g (σ .resultSort o) (coeRes X o z) ≡ coeRes Y o w

open SigMapᶠ

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} where

  idSigMapᶠ : SigMapᶠ ℓX σ σ
  idSigMapᶠ .onOps o = o
  idSigMapᶠ .unArity o a = a
  idSigMapᶠ .coeArg X o a z = z
  idSigMapᶠ .coeRes X o z = z
  idSigMapᶠ .natArg X Y g o a z w p = p
  idSigMapᶠ .natRes X Y g o z w p = p

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {υ : SortedSig S ℓ3 ℓ3'} (F : SigMapᶠ ℓX σ τ) (G : SigMapᶠ ℓX τ υ)
  where

  -- composition is function composition in every field, so all three
  -- category laws below are `refl`
  _⋆SigMapᶠ_ : SigMapᶠ ℓX σ υ
  _⋆SigMapᶠ_ .onOps o = G .onOps (F .onOps o)
  _⋆SigMapᶠ_ .unArity o a = F .unArity o (G .unArity (F .onOps o) a)
  _⋆SigMapᶠ_ .coeArg X o a z =
    G .coeArg X (F .onOps o) a
      (F .coeArg X o (G .unArity (F .onOps o) a) z)
  _⋆SigMapᶠ_ .coeRes X o z =
    F .coeRes X o (G .coeRes X (F .onOps o) z)
  _⋆SigMapᶠ_ .natArg X Y g o a z w p =
    G .natArg X Y g (F .onOps o) a _ _
      (F .natArg X Y g o (G .unArity (F .onOps o) a) z w p)
  _⋆SigMapᶠ_ .natRes X Y g o z w p =
    F .natRes X Y g o _ _ (G .natRes X Y g (F .onOps o) z w p)

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (F : SigMapᶠ ℓX σ τ) where

  ⋆SigMapᶠIdL : (idSigMapᶠ ⋆SigMapᶠ F) ≡ F
  ⋆SigMapᶠIdL = refl

  ⋆SigMapᶠIdR : (F ⋆SigMapᶠ idSigMapᶠ) ≡ F
  ⋆SigMapᶠIdR = refl

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {υ : SortedSig S ℓ3 ℓ3'} {ν : SortedSig S ℓ ℓ'}
  (F : SigMapᶠ ℓX σ τ) (G : SigMapᶠ ℓX τ υ) (H : SigMapᶠ ℓX υ ν) where

  ⋆SigMapᶠAssoc :
    ((F ⋆SigMapᶠ G) ⋆SigMapᶠ H) ≡ (F ⋆SigMapᶠ (G ⋆SigMapᶠ H))
  ⋆SigMapᶠAssoc = refl

-- every honest signature map -- one that ships the two sort equations
-- as `Eq.≡` fords -- gives a `SigMapᶠ`, with `Eq.transport` for the
-- coercions and `Eq.J` for their naturality
natEqᶠ : {S : Type ℓS} {X Y : S → hSet ℓX}
  (g : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
  {s s' : S} (p : s Eq.≡ s') {z : ⟨ X s ⟩} {w : ⟨ Y s ⟩}
  → g s z ≡ w
  → g s' (Eq.transport (λ t → ⟨ X t ⟩) p z)
    ≡ Eq.transport (λ t → ⟨ Y t ⟩) p w
natEqᶠ g Eq.refl q = q

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (F : Mor.SortedSigMap σ τ) where

  private module F = Mor.SortedSigMap F

  fromSortedSigMap : SigMapᶠ ℓX σ τ
  fromSortedSigMap .onOps = F.onOps
  fromSortedSigMap .unArity = F.unArity
  fromSortedSigMap .coeArg X o a =
    Eq.transport (λ s → ⟨ X s ⟩) (F.onSortOf o a)
  fromSortedSigMap .coeRes X o =
    Eq.transport (λ s → ⟨ X s ⟩) (Eq.sym (F.onResult o))
  fromSortedSigMap .natArg X Y g o a z w = natEqᶠ g (F.onSortOf o a)
  fromSortedSigMap .natRes X Y g o z w = natEqᶠ g (Eq.sym (F.onResult o))

-- ------------------------------------------------------------------
-- restriction of interpretations along a `SigMapᶠ`
-- ------------------------------------------------------------------

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (F : SigMapᶠ ℓX σ τ) where

  resOpsᶠ : (X : S → hSet ℓX)
    → Ops {σ = τ} (λ s → ⟨ X s ⟩) → Ops {σ = σ} (λ s → ⟨ X s ⟩)
  resOpsᶠ X α o x =
    F .coeRes X o
      (α (F .onOps o) (λ a → F .coeArg X o a (x (F .unArity o a))))

-- and it agrees with the restriction along the underlying honest map
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (F : Mor.SortedSigMap σ τ) (X : S → hSet ℓX)
  (α : Ops {σ = τ} (λ s → ⟨ X s ⟩)) where

  resOpsᶠ-fromSortedSigMap :
    resOpsᶠ (fromSortedSigMap F) X α ≡ Mor.resOps F (λ s → ⟨ X s ⟩) α
  resOpsᶠ-fromSortedSigMap = refl

-- restriction is a *strict* functor of interpretations: this is the
-- whole point of storing the coercions rather than the equations
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} (X : S → hSet ℓX)
  (α : Ops {σ = σ} (λ s → ⟨ X s ⟩)) where

  resOpsᶠId : resOpsᶠ (idSigMapᶠ {σ = σ}) X α ≡ α
  resOpsᶠId = refl

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {υ : SortedSig S ℓ3 ℓ3'} (F : SigMapᶠ ℓX σ τ) (G : SigMapᶠ ℓX τ υ)
  (X : S → hSet ℓX) (α : Ops {σ = υ} (λ s → ⟨ X s ⟩)) where

  resOpsᶠ⋆ : resOpsᶠ (F ⋆SigMapᶠ G) X α ≡ resOpsᶠ F X (resOpsᶠ G X α)
  resOpsᶠ⋆ = refl

-- ------------------------------------------------------------------
-- the category of sorted signatures over a fixed sort set
-- ------------------------------------------------------------------

module _ {S : Type ℓS} (ℓX : Level)
  (σ : SortedSig S ℓ1 ℓ1') (τ : SortedSig S ℓ2 ℓ2') where

  SigMapᶠΣ : Type _
  SigMapᶠΣ =
    Σ[ f ∈ (σ .ops → τ .ops) ]
    Σ[ u ∈ ((o : σ .ops) → τ .arities (f o) → σ .arities o) ]
    Σ[ cA ∈ ((X : S → hSet ℓX) (o : σ .ops) (a : τ .arities (f o))
             → ⟨ X (σ .sortOf o (u o a)) ⟩ → ⟨ X (τ .sortOf (f o) a) ⟩) ]
    Σ[ cR ∈ ((X : S → hSet ℓX) (o : σ .ops)
             → ⟨ X (τ .resultSort (f o)) ⟩ → ⟨ X (σ .resultSort o) ⟩) ]
      (((X Y : S → hSet ℓX) (g : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
        (o : σ .ops) (a : τ .arities (f o))
        (z : ⟨ X (σ .sortOf o (u o a)) ⟩)
        (w : ⟨ Y (σ .sortOf o (u o a)) ⟩)
        → g (σ .sortOf o (u o a)) z ≡ w
        → g (τ .sortOf (f o) a) (cA X o a z) ≡ cA Y o a w)
      × ((X Y : S → hSet ℓX) (g : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
        (o : σ .ops)
        (z : ⟨ X (τ .resultSort (f o)) ⟩)
        (w : ⟨ Y (τ .resultSort (f o)) ⟩)
        → g (τ .resultSort (f o)) z ≡ w
        → g (σ .resultSort o) (cR X o z) ≡ cR Y o w))

  SigMapᶠIsoΣ : Iso (SigMapᶠ ℓX σ τ) SigMapᶠΣ
  SigMapᶠIsoΣ .Iso.fun F =
    F .onOps , F .unArity , F .coeArg , F .coeRes , F .natArg , F .natRes
  SigMapᶠIsoΣ .Iso.inv (f , u , cA , cR , nA , nR) .onOps = f
  SigMapᶠIsoΣ .Iso.inv (f , u , cA , cR , nA , nR) .unArity = u
  SigMapᶠIsoΣ .Iso.inv (f , u , cA , cR , nA , nR) .coeArg = cA
  SigMapᶠIsoΣ .Iso.inv (f , u , cA , cR , nA , nR) .coeRes = cR
  SigMapᶠIsoΣ .Iso.inv (f , u , cA , cR , nA , nR) .natArg = nA
  SigMapᶠIsoΣ .Iso.inv (f , u , cA , cR , nA , nR) .natRes = nR
  SigMapᶠIsoΣ .Iso.sec _ = refl
  SigMapᶠIsoΣ .Iso.ret _ = refl

  isSetSigMapᶠ : isSet (τ .ops) → ((o : σ .ops) → isSet (σ .arities o))
    → isSet (SigMapᶠ ℓX σ τ)
  isSetSigMapᶠ isSetOpsτ isSetArσ =
    isOfHLevelRetractFromIso 2 SigMapᶠIsoΣ
      (isSetΣ (isSet→ isSetOpsτ) λ f →
       isSetΣ (isSetΠ2 (λ o a → isSetArσ o)) λ u →
       isSetΣ (isSetΠ λ X → isSetΠ2 λ o a → isSet→ (X _ .snd)) λ cA →
       isSetΣ (isSetΠ2 λ X o → isSet→ (X _ .snd)) λ cR →
       isSet×
         (isSetΠ λ X → isSetΠ λ Y → isSetΠ λ g → isSetΠ λ o → isSetΠ λ a →
          isSetΠ λ z → isSetΠ λ w → isSetΠ λ _ →
          isProp→isSet (Y _ .snd _ _))
         (isSetΠ λ X → isSetΠ λ Y → isSetΠ λ g → isSetΠ λ o →
          isSetΠ λ z → isSetΠ λ w → isSetΠ λ _ →
          isProp→isSet (Y _ .snd _ _)))

record SetSortedSig (S : Type ℓS) (ℓ ℓ' : Level)
  : Type (ℓ-max ℓS (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))) where
  field
    sig : SortedSig S ℓ ℓ'
    isSetOps : isSet (sig .ops)
    isSetArities : (o : sig .ops) → isSet (sig .arities o)

open SetSortedSig

SORTEDSIG : (S : Type ℓS) (ℓ ℓ' ℓX : Level) → Category _ _
SORTEDSIG S ℓ ℓ' ℓX .Category.ob = SetSortedSig S ℓ ℓ'
SORTEDSIG S ℓ ℓ' ℓX .Category.Hom[_,_] σ τ = SigMapᶠ ℓX (σ .sig) (τ .sig)
SORTEDSIG S ℓ ℓ' ℓX .Category.id = idSigMapᶠ
SORTEDSIG S ℓ ℓ' ℓX .Category._⋆_ = _⋆SigMapᶠ_
SORTEDSIG S ℓ ℓ' ℓX .Category.⋆IdL f = refl
SORTEDSIG S ℓ ℓ' ℓX .Category.⋆IdR f = refl
SORTEDSIG S ℓ ℓ' ℓX .Category.⋆Assoc f g h = refl
SORTEDSIG S ℓ ℓ' ℓX .Category.isSetHom {x = σ} {y = τ} =
  isSetSigMapᶠ ℓX (σ .sig) (τ .sig) (τ .isSetOps) (σ .isSetArities)

-- ------------------------------------------------------------------
-- the category of sorted theories: equations displayed over signatures
-- ------------------------------------------------------------------

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (σeq : SortedEqns σ ℓ'' ℓv) (τeq : SortedEqns τ ℓ'' ℓv) (ℓX : Level)
  (F : SigMapᶠ ℓX σ τ) where

  -- every σ-equation holds in the restriction of every τ-model
  PresEqnsᶠ : Type _
  PresEqnsᶠ = (M : Category.ob (MOD τeq ℓX))
    (e : σeq .eqns) (ρ : (v : σeq .vars e) → ⟨ M .fst (σeq .varSort e v) ⟩)
    → TmRec (λ s → ⟨ M .fst s ⟩)
        (resOpsᶠ F (M .fst) (M .snd .fst)) ρ (σeq .lhs e)
      ≡ TmRec (λ s → ⟨ M .fst s ⟩)
          (resOpsᶠ F (M .fst) (M .snd .fst)) ρ (σeq .rhs e)

  isPropPresEqnsᶠ : isProp PresEqnsᶠ
  isPropPresEqnsᶠ =
    isPropΠ3 (λ M e _ → M .fst (σeq .eqnSort e) .snd _ _)

  module _ (pres : PresEqnsᶠ) where

    resModObᶠ : Category.ob (MOD τeq ℓX) → Category.ob (MOD σeq ℓX)
    resModObᶠ M = M .fst , resOpsᶠ F (M .fst) (M .snd .fst) , pres M

SORTEDTHEORYᴰ : (S : Type ℓS) (ℓ ℓ' ℓ'' ℓv ℓX : Level)
  → Categoryᴰ (SORTEDSIG S ℓ ℓ' ℓX) _ _
SORTEDTHEORYᴰ S ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.ob[_] σ =
  SortedEqns (σ .sig) ℓ'' ℓv
SORTEDTHEORYᴰ S ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.Hom[_][_,_] F σeq τeq =
  PresEqnsᶠ σeq τeq ℓX F
SORTEDTHEORYᴰ S ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.idᴰ M e ρ = M .snd .snd e ρ
SORTEDTHEORYᴰ S ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ._⋆ᴰ_
  {g = G} {yᴰ = τeq} {zᴰ = υeq} pF pG M e ρ =
  pF (resModObᶠ τeq υeq ℓX G pG M) e ρ
SORTEDTHEORYᴰ S ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.⋆IdLᴰ pF = refl
SORTEDTHEORYᴰ S ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.⋆IdRᴰ pF = refl
SORTEDTHEORYᴰ S ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.⋆Assocᴰ pF pG pH = refl
SORTEDTHEORYᴰ S ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.isSetHomᴰ
  {xᴰ = σeq} {yᴰ = τeq} =
  isProp→isSet (isPropPresEqnsᶠ σeq τeq ℓX _)

SORTEDTHEORY : (S : Type ℓS) (ℓ ℓ' ℓ'' ℓv ℓX : Level) → Category _ _
SORTEDTHEORY S ℓ ℓ' ℓ'' ℓv ℓX = ∫C (SORTEDTHEORYᴰ S ℓ ℓ' ℓ'' ℓv ℓX)

-- ------------------------------------------------------------------
-- END LOCAL SCAFFOLDING
-- ------------------------------------------------------------------

-- ------------------------------------------------------------------
-- restriction of homomorphisms
--
-- This is the one place in this file that is not `refl`, and it cannot
-- be made `refl` by any further fording of the signature map.  `ALGᴰ`'s
-- homomorphism condition is forded in the *result*
--
--     (o) (x) (y) → y ≡ α o x → f _ y ≡ β o (λ a → f _ (x a))
--
-- but not in the *arguments*: the arguments of `β` are pinned to be
-- `λ a → f _ (x a)`.  Restricting the condition along `F` has to
-- exchange `f (coeArg z)` for `coeArg (f z)` underneath `γ (F o) (—)`,
-- which is a rewrite at an argument position -- hence the
-- `cong (γ (F .onOps o)) (funExt (λ a → F .natArg ...))` below, and the
-- two `_∙_`s chaining it.  `_∙_` has no strict unit, so
-- `resHomCondᶠ` of the identity homomorphism condition is
-- `eq ∙ refl ∙ refl`, not `eq`, and `MODOVERᴰ`'s unit laws are
-- therefore propositional.  Making them `refl` would require editing
-- `ALGᴰ` -- fording the argument positions too, and having the
-- conclusion be *consumed* rather than produced -- which this file may
-- not do.
-- ------------------------------------------------------------------

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (F : SigMapᶠ ℓX σ τ) (X Y : S → hSet ℓX)
  (g : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
  (β : Ops {σ = τ} (λ s → ⟨ X s ⟩)) (γ : Ops {σ = τ} (λ s → ⟨ Y s ⟩))
  (ψ : Categoryᴰ.Hom[_][_,_] (ALGᴰ τ ℓX) {x = X} {y = Y} g β γ) where

  resHomCondᶠ :
    Categoryᴰ.Hom[_][_,_] (ALGᴰ σ ℓX) {x = X} {y = Y} g
      (resOpsᶠ F X β) (resOpsᶠ F Y γ)
  resHomCondᶠ o x y eq =
    cong (g (σ .resultSort o)) eq
    ∙ F .natRes X Y g o (β (F .onOps o) w)
        (γ (F .onOps o) (λ a → F .coeArg Y o a (g _ (x (F .unArity o a)))))
        (ψ (F .onOps o) w (β (F .onOps o) w) refl
         ∙ cong (γ (F .onOps o))
             (funExt (λ a →
               F .natArg X Y g o a (x (F .unArity o a)) _ refl)))
    where
      w : (a : τ .arities (F .onOps o)) → ⟨ X (τ .sortOf (F .onOps o) a) ⟩
      w a = F .coeArg X o a (x (F .unArity o a))

isPropModHomᴰ : {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'}
  {σeq : SortedEqns σ ℓ'' ℓv} {ℓX : Level}
  (M N : Category.ob (MOD σeq ℓX))
  (f : (s : S) → ⟨ M .fst s ⟩ → ⟨ N .fst s ⟩)
  → isProp (Categoryᴰ.Hom[_][_,_] (MODᴰ σeq ℓX)
      {x = M .fst} {y = N .fst} f (M .snd) (N .snd))
isPropModHomᴰ M N f =
  isPropΣ (isPropΠ4 (λ _ _ _ _ → N .fst _ .snd _ _)) (λ _ → isPropUnit*)

-- ------------------------------------------------------------------
-- models displayed over theories
-- ------------------------------------------------------------------

module _ (S : Type ℓS) (ℓ ℓ' ℓ'' ℓv : Level) where
  private
    ℓF = ℓFree ℓS ℓ ℓ' ℓ'' ℓv

  TH : Category _ _
  TH = SORTEDTHEORY S ℓ ℓ' ℓ'' ℓv ℓF

  private module TH = Category TH

  thy : (T : TH.ob) → SortedEqns (T .fst .sig) ℓ'' ℓv
  thy T = T .snd

  module _ {T U : TH.ob} (h : TH.Hom[ T , U ]) where

    reOb : Category.ob (MOD (thy U) ℓF) → Category.ob (MOD (thy T) ℓF)
    reOb = resModObᶠ (thy T) (thy U) ℓF (h .fst) (h .snd)

    reHom : (N P : Category.ob (MOD (thy U) ℓF))
      → ModHom (thy U) ℓF N P → ModHom (thy T) ℓF (reOb N) (reOb P)
    reHom N P ψ =
      ψ .fst
      , resHomCondᶠ (h .fst) (N .fst) (P .fst) (ψ .fst)
          (N .snd .fst) (P .snd .fst) (ψ .snd .fst)
      , tt*

    ReindexMod : Functor (MOD (thy U) ℓF) (MOD (thy T) ℓF)
    ReindexMod .Functor.F-ob = reOb
    ReindexMod .Functor.F-hom {x = N} {y = P} = reHom N P
    ReindexMod .Functor.F-id {x = N} =
      Σ≡Prop (isPropModHomᴰ (reOb N) (reOb N)) refl
    ReindexMod .Functor.F-seq {x = N} {y = P} {z = Q} ψ χ =
      Σ≡Prop (isPropModHomᴰ (reOb N) (reOb Q)) refl

  -- `Hom[ h ][ M , N ]` is a homomorphism of `T`-models from `M` to the
  -- restriction of `N` along `h`; `reOb` is strictly functorial, so the
  -- source and target of `_⋆ᴰ_` line up on the nose and no transport
  -- appears anywhere.  The three laws are *not* `refl`, and this is the
  -- one residual non-strictness in this file: see the comment on
  -- `resHomCondᶠ`.  They do hold as honest paths, and by `Σ≡Prop` with
  -- `refl` on the underlying function -- the displayed hom is a
  -- function together with a *proposition*, and composition of the
  -- function components is literal function composition.
  MODOVERᴰ : Categoryᴰ TH _ _
  MODOVERᴰ .Categoryᴰ.ob[_] T = Category.ob (MOD (thy T) ℓF)
  MODOVERᴰ .Categoryᴰ.Hom[_][_,_] {x = T} {y = U} h M N =
    ModHom (thy T) ℓF M (reOb {T = T} {U = U} h N)
  MODOVERᴰ .Categoryᴰ.idᴰ {x = T} {p = M} =
    Category.id (MOD (thy T) ℓF) {x = M}
  MODOVERᴰ .Categoryᴰ._⋆ᴰ_ {x = T} {y = U} {z = W} {f = h} {g = k}
    {xᴰ = M} {yᴰ = N} {zᴰ = P} ϕ ψ =
    Category._⋆_ (MOD (thy T) ℓF)
      {x = M} {y = reOb h N}
      {z = reOb h (reOb k P)}
      ϕ (reHom h N (reOb k P) ψ)
  MODOVERᴰ .Categoryᴰ.⋆IdLᴰ {x = T} {y = U} {f = h} {xᴰ = M} {yᴰ = N} ϕ =
    Σ≡Prop (isPropModHomᴰ M (reOb h N)) refl
  MODOVERᴰ .Categoryᴰ.⋆IdRᴰ {x = T} {y = U} {f = h} {xᴰ = M} {yᴰ = N} ϕ =
    Σ≡Prop (isPropModHomᴰ M (reOb h N)) refl
  MODOVERᴰ .Categoryᴰ.⋆Assocᴰ {x = T} {f = h} {g = k} {h = l}
    {xᴰ = M} {yᴰ = N} {zᴰ = P} {wᴰ = Q} ϕ ψ χ =
    Σ≡Prop
      (isPropModHomᴰ M
        (reOb (TH._⋆_ h (TH._⋆_ k l)) Q))
      refl
  MODOVERᴰ .Categoryᴰ.isSetHomᴰ {x = T} {y = U} {f = h} {xᴰ = M} {yᴰ = N} =
    Category.isSetHom (MOD (thy T) ℓF) {x = M} {y = reOb h N}

  -- ----------------------------------------------------------------
  -- the free model, as a global section: natural in the theory
  -- ----------------------------------------------------------------

  module _ (V : Type ℓv) (vs : V → S) where

    freeHom : {T U : TH.ob} (h : TH.Hom[ T , U ])
      → ModHom (thy T) ℓF (FreeOb (thy T) V vs)
          (reOb {T = T} {U = U} h (FreeOb (thy U) V vs))
    freeHom {T} {U} h =
      Iso.inv (UPMod (thy T) V vs (reOb h (FreeOb (thy U) V vs)))
        (λ v → gen v)

    FreeSection : GlobalSection MODOVERᴰ
    FreeSection .Section.F-obᴰ T = FreeOb (thy T) V vs
    FreeSection .Section.F-homᴰ {T} {U} h = freeHom {T} {U} h
    FreeSection .Section.F-idᴰ {T} =
      isoFunInjective (UPMod (thy T) V vs (FreeOb (thy T) V vs))
        (freeHom {T} {T} (TH.id {T}))
        (Category.id (MOD (thy T) ℓF) {x = FreeOb (thy T) V vs})
        refl
    FreeSection .Section.F-seqᴰ {T} {U} {W} h k =
      isoFunInjective
        (UPMod (thy T) V vs
          (reOb (TH._⋆_ {x = T} {y = U} {z = W} h k)
            (FreeOb (thy W) V vs)))
        (freeHom {T} {W} (TH._⋆_ {x = T} {y = U} {z = W} h k))
        (Categoryᴰ._⋆ᴰ_ MODOVERᴰ {f = h} {g = k}
          (freeHom {T} {U} h) (freeHom {U} {W} k))
        refl

  -- Initiality of the syntax, generically in the theory: the section
  -- at the empty generating set picks out the initial model of *every*
  -- theory, naturally in the theory.
  InitialSection : GlobalSection MODOVERᴰ
  InitialSection = FreeSection (⊥* {ℓv}) (λ ())

  isInitialInitialSection : (T : TH.ob)
    → isInitial (MOD (thy T) ℓF) (Section.F-obᴰ InitialSection T)
  isInitialInitialSection T = isInitialFreeOb (thy T)
