{-# OPTIONS --lossy-unification #-}
-- The category of many-sorted theories over a fixed sort set.
--
-- `Sorted.Morphism` has all the ingredients -- `SortedSigMap`,
-- `idSortedSigMap`, `_⋆SigMap_`, `PresEqns` -- but never assembles them,
-- and it cannot: with the sort coherences stored as `Eq.≡` proofs,
-- composition chains them with `Eq._∙_`, which recurses on its *first*
-- argument, so `Eq.refl Eq.∙ p` reduces but `p Eq.∙ Eq.refl` does not.
-- Only the left unit law is `refl`.
--
-- The fix is to change how the coherences are stored, not to accept
-- propositional laws.  A `SortedSigMapᶠ` carries its sort coherences in
-- Yoneda (continuation) form: instead of a proof
--
--     σ .resultSort o Eq.≡ τ .resultSort (onOps o)
--
-- it carries, for every sort `s`, a *function*
--
--     s Eq.≡ τ .resultSort (onOps o) → s Eq.≡ σ .resultSort o
--
-- and dually for arguments.  Composing two signature maps then composes
-- these functions, and function composition is strictly unital and
-- strictly associative.  All three category laws of `SORTEDSIG` are
-- `refl`, exactly as in the single-sorted `SIG`.
--
-- The same move is needed one level up.  `Morphism.agda`'s `resOps`
-- *transports* along the coherences, and transport along a composite
-- proof is not the composite of the transports, so restriction of
-- models is only pseudo-functorial.  Restricting instead on the
-- transport-closed carrier `Cay X` -- where a transport is proof
-- plumbing rather than computation -- makes restriction strictly
-- functorial (`resOpsᶜ-id` and `resOpsᶜ-⋆` are `refl`), and hence makes
-- all three laws of `SORTEDTHEORYᴰ`, and of the total category
-- `SORTEDTHEORY`, `refl` as well.  `Cay X ≃ X`, so this is a change of
-- presentation and not of content: `presᶜ→pres` turns a preservation
-- proof back into `Morphism.agda`'s `PresEqns`.
module Cubical.Algebra.Theory.Sorted.Theories where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Instances.TotalCategory

open import Cubical.Algebra.Theory.Sorted
open import Cubical.Algebra.Theory.Sorted.Morphism

private
  variable
    ℓS ℓ ℓ' ℓ1 ℓ1' ℓ2 ℓ2' ℓ3 ℓ3' ℓ4 ℓ4' : Level
    ℓ'' ℓ1'' ℓ2'' ℓ3'' ℓv ℓw ℓX : Level

open SortedSig
open SortedEqns
open Functor
open SortedSigMap renaming
  ( onOps to onOpsᴹ ; unArity to unArityᴹ
  ; onSortOf to onSortOfᴹ ; onResult to onResultᴹ )

-- ------------------------------------------------------------------
-- Signature maps, forded in Yoneda form
-- ------------------------------------------------------------------

record SortedSigMapᶠ {S : Type ℓS}
  (σ : SortedSig S ℓ1 ℓ1') (τ : SortedSig S ℓ2 ℓ2')
  : Type (ℓ-max ℓS (ℓ-max ℓ1 (ℓ-max ℓ2 (ℓ-max ℓ1' ℓ2')))) where
  field
    onOps : σ .ops → τ .ops
    unArity : (o : σ .ops) → τ .arities (onOps o) → σ .arities o
    -- arguments are pushed forward, results are pulled back
    onSortOf : (o : σ .ops) (a : τ .arities (onOps o)) (s : S)
      → s Eq.≡ σ .sortOf o (unArity o a)
      → s Eq.≡ τ .sortOf (onOps o) a
    onResult : (o : σ .ops) (s : S)
      → s Eq.≡ τ .resultSort (onOps o)
      → s Eq.≡ σ .resultSort o

open SortedSigMapᶠ

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} where

  idSortedSigMapᶠ : SortedSigMapᶠ σ σ
  idSortedSigMapᶠ .onOps o = o
  idSortedSigMapᶠ .unArity o a = a
  idSortedSigMapᶠ .onSortOf o a s e = e
  idSortedSigMapᶠ .onResult o s e = e

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {υ : SortedSig S ℓ3 ℓ3'} (F : SortedSigMapᶠ σ τ)
  (G : SortedSigMapᶠ τ υ) where

  _⋆SigMapᶠ_ : SortedSigMapᶠ σ υ
  _⋆SigMapᶠ_ .onOps o = G .onOps (F .onOps o)
  _⋆SigMapᶠ_ .unArity o a = F .unArity o (G .unArity (F .onOps o) a)
  _⋆SigMapᶠ_ .onSortOf o a s e =
    G .onSortOf (F .onOps o) a s
      (F .onSortOf o (G .unArity (F .onOps o) a) s e)
  _⋆SigMapᶠ_ .onResult o s e =
    F .onResult o s (G .onResult (F .onOps o) s e)

-- All three laws are `refl`: composition of signature maps is
-- composition of functions in the coherence components.
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (F : SortedSigMapᶠ σ τ) where

  ⋆SigMapᶠIdL : (idSortedSigMapᶠ ⋆SigMapᶠ F) ≡ F
  ⋆SigMapᶠIdL = refl

  ⋆SigMapᶠIdR : (F ⋆SigMapᶠ idSortedSigMapᶠ) ≡ F
  ⋆SigMapᶠIdR = refl

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {υ : SortedSig S ℓ3 ℓ3'} {ν : SortedSig S ℓ4 ℓ4'}
  (F : SortedSigMapᶠ σ τ) (G : SortedSigMapᶠ τ υ)
  (H : SortedSigMapᶠ υ ν) where

  ⋆SigMapᶠAssoc :
    ((F ⋆SigMapᶠ G) ⋆SigMapᶠ H) ≡ (F ⋆SigMapᶠ (G ⋆SigMapᶠ H))
  ⋆SigMapᶠAssoc = refl

-- ------------------------------------------------------------------
-- Paths between signature maps
-- ------------------------------------------------------------------
--
-- The coherences are Π-types into `Eq.≡` in `S`, so as soon as `S` is a
-- set they are propositions and only `onOps`/`unArity` are compared.
module _ {S : Type ℓS} (isSetS : isSet S) where

  isPropEqS : {s s' : S} → isProp (s Eq.≡ s')
  isPropEqS {s} {s'} = subst isProp Eq.PathPathEq (isSetS s s')

  module _ {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
    {F G : SortedSigMapᶠ σ τ}
    (p : F .onOps ≡ G .onOps)
    (q : PathP (λ i → (o : σ .ops) → τ .arities (p i o) → σ .arities o)
           (F .unArity) (G .unArity)) where

    SortedSigMapᶠ≡ : F ≡ G
    SortedSigMapᶠ≡ i .onOps = p i
    SortedSigMapᶠ≡ i .unArity = q i
    SortedSigMapᶠ≡ i .onSortOf =
      isProp→PathP
        {B = λ i → (o : σ .ops) (a : τ .arities (p i o)) (s : S)
                 → s Eq.≡ σ .sortOf o (q i o a)
                 → s Eq.≡ τ .sortOf (p i o) a}
        (λ i → isPropΠ4 (λ o a s e → isPropEqS))
        (F .onSortOf) (G .onSortOf) i
    SortedSigMapᶠ≡ i .onResult =
      isProp→PathP
        {B = λ i → (o : σ .ops) (s : S)
                 → s Eq.≡ τ .resultSort (p i o)
                 → s Eq.≡ σ .resultSort o}
        (λ i → isPropΠ3 (λ o s e → isPropEqS))
        (F .onResult) (G .onResult) i

  module _ {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'} where

    SortedSigMapᶠΣ : Type (ℓ-max ℓS (ℓ-max ℓ1 (ℓ-max ℓ2 (ℓ-max ℓ1' ℓ2'))))
    SortedSigMapᶠΣ =
      Σ[ h ∈ (σ .ops → τ .ops) ]
      Σ[ u ∈ ((o : σ .ops) → τ .arities (h o) → σ .arities o) ]
      Σ[ _ ∈ ((o : σ .ops) (a : τ .arities (h o)) (s : S)
              → s Eq.≡ σ .sortOf o (u o a) → s Eq.≡ τ .sortOf (h o) a) ]
      ((o : σ .ops) (s : S)
        → s Eq.≡ τ .resultSort (h o) → s Eq.≡ σ .resultSort o)

    SortedSigMapᶠIsoΣ : Iso (SortedSigMapᶠ σ τ) SortedSigMapᶠΣ
    SortedSigMapᶠIsoΣ .Iso.fun F =
      F .onOps , F .unArity , F .onSortOf , F .onResult
    SortedSigMapᶠIsoΣ .Iso.inv (h , u , c , r) .onOps = h
    SortedSigMapᶠIsoΣ .Iso.inv (h , u , c , r) .unArity = u
    SortedSigMapᶠIsoΣ .Iso.inv (h , u , c , r) .onSortOf = c
    SortedSigMapᶠIsoΣ .Iso.inv (h , u , c , r) .onResult = r
    SortedSigMapᶠIsoΣ .Iso.sec _ = refl
    SortedSigMapᶠIsoΣ .Iso.ret _ = refl

    isSetSortedSigMapᶠ : isSet (τ .ops)
      → ((o : σ .ops) → isSet (σ .arities o))
      → isSet (SortedSigMapᶠ σ τ)
    isSetSortedSigMapᶠ isSetτops isSetσar =
      isOfHLevelRetractFromIso 2 SortedSigMapᶠIsoΣ
        (isSetΣ (isSet→ isSetτops) (λ h →
          isSetΣ (isSetΠ (λ o → isSet→ (isSetσar o))) (λ u →
            isSetΣ (isProp→isSet (isPropΠ4 (λ _ _ _ _ → isPropEqS)))
              (λ _ → isProp→isSet (isPropΠ3 (λ _ _ _ → isPropEqS))))))

-- ------------------------------------------------------------------
-- The category of sorted signatures
-- ------------------------------------------------------------------

record SortedSetSig (S : Type ℓS) ℓ ℓ'
  : Type (ℓ-max ℓS (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))) where
  field
    sig : SortedSig S ℓ ℓ'
    isSetOps : isSet (sig .ops)
    isSetArities : (o : sig .ops) → isSet (sig .arities o)

open SortedSetSig

module _ {S : Type ℓS} (isSetS : isSet S) where

  SORTEDSIG : ∀ ℓ ℓ'
    → Category (ℓ-max ℓS (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')))
               (ℓ-max ℓS (ℓ-max ℓ ℓ'))
  SORTEDSIG ℓ ℓ' .Category.ob = SortedSetSig S ℓ ℓ'
  SORTEDSIG ℓ ℓ' .Category.Hom[_,_] σ τ =
    SortedSigMapᶠ (σ .sig) (τ .sig)
  SORTEDSIG ℓ ℓ' .Category.id = idSortedSigMapᶠ
  SORTEDSIG ℓ ℓ' .Category._⋆_ = _⋆SigMapᶠ_
  SORTEDSIG ℓ ℓ' .Category.⋆IdL F = refl
  SORTEDSIG ℓ ℓ' .Category.⋆IdR F = refl
  SORTEDSIG ℓ ℓ' .Category.⋆Assoc F G H = refl
  SORTEDSIG ℓ ℓ' .Category.isSetHom {x = σ} {y = τ} =
    isSetSortedSigMapᶠ isSetS (τ .isSetOps) (σ .isSetArities)

-- ------------------------------------------------------------------
-- Comparison with `Morphism.agda`'s `SortedSigMap`
-- ------------------------------------------------------------------
--
-- Nothing already built is orphaned: the Yoneda-forded maps translate
-- back and forth with the `Eq.≡`-forded ones, so `resOps`, `PresEqns`,
-- `resHomCond` and `resMod` all apply to a `SortedSigMapᶠ` through
-- `toSortedSigMap`.
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  where

  toSortedSigMap : SortedSigMapᶠ σ τ → SortedSigMap σ τ
  toSortedSigMap F .onOpsᴹ = F .onOps
  toSortedSigMap F .unArityᴹ = F .unArity
  toSortedSigMap F .onSortOfᴹ o a = F .onSortOf o a _ Eq.refl
  toSortedSigMap F .onResultᴹ o = Eq.sym (F .onResult o _ Eq.refl)

  fromSortedSigMap : SortedSigMap σ τ → SortedSigMapᶠ σ τ
  fromSortedSigMap F .onOps = F .onOpsᴹ
  fromSortedSigMap F .unArity = F .unArityᴹ
  fromSortedSigMap F .onSortOf o a s e = e Eq.∙ F .onSortOfᴹ o a
  fromSortedSigMap F .onResult o s e = e Eq.∙ Eq.sym (F .onResultᴹ o)

-- `toSortedSigMap` takes identities to identities on the nose.
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} where
  toSortedSigMap-id :
    toSortedSigMap (idSortedSigMapᶠ {σ = σ}) ≡ idSortedSigMap
  toSortedSigMap-id = refl

module _ {S : Type ℓS} (isSetS : isSet S)
  {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'} where

  -- the analogue of `SortedSigMapᶠ≡` for `Morphism.agda`'s record
  module _ {F G : SortedSigMap σ τ}
    (p : F .onOpsᴹ ≡ G .onOpsᴹ)
    (q : PathP (λ i → (o : σ .ops) → τ .arities (p i o) → σ .arities o)
           (F .unArityᴹ) (G .unArityᴹ)) where

    SortedSigMap≡ : F ≡ G
    SortedSigMap≡ i .onOpsᴹ = p i
    SortedSigMap≡ i .unArityᴹ = q i
    SortedSigMap≡ i .onSortOfᴹ =
      isProp→PathP
        {B = λ i → (o : σ .ops) (a : τ .arities (p i o))
                 → σ .sortOf o (q i o a) Eq.≡ τ .sortOf (p i o) a}
        (λ i → isPropΠ2 (λ o a → isPropEqS isSetS))
        (F .onSortOfᴹ) (G .onSortOfᴹ) i
    SortedSigMap≡ i .onResultᴹ =
      isProp→PathP
        {B = λ i → (o : σ .ops)
                 → σ .resultSort o Eq.≡ τ .resultSort (p i o)}
        (λ i → isPropΠ (λ o → isPropEqS isSetS))
        (F .onResultᴹ) (G .onResultᴹ) i

  -- the round trips.  `to ∘ from` is `refl` on `onOps`, `unArity` and
  -- `onSortOf` -- `Eq.refl Eq.∙ p` reduces -- but not on `onResult`,
  -- where it leaves `Eq.sym (Eq.sym p)`; both are settled by the sort
  -- coherences being propositions.
  toFromSortedSigMap : (F : SortedSigMap σ τ)
    → toSortedSigMap (fromSortedSigMap F) ≡ F
  toFromSortedSigMap F = SortedSigMap≡ refl refl

  fromToSortedSigMap : (F : SortedSigMapᶠ σ τ)
    → fromSortedSigMap (toSortedSigMap F) ≡ F
  fromToSortedSigMap F = SortedSigMapᶠ≡ isSetS refl refl

module _ {S : Type ℓS} (isSetS : isSet S)
  {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {υ : SortedSig S ℓ3 ℓ3'}
  (F : SortedSigMapᶠ σ τ) (G : SortedSigMapᶠ τ υ) where

  toSortedSigMap-⋆ : toSortedSigMap (F ⋆SigMapᶠ G)
    ≡ (toSortedSigMap F ⋆SigMap toSortedSigMap G)
  toSortedSigMap-⋆ = SortedSigMap≡ isSetS refl refl

-- ------------------------------------------------------------------
-- Restriction of interpretations, strictly
-- ------------------------------------------------------------------
--
-- `Morphism.agda`'s `resOps` transports along the sort coherences, and
-- transport along a *composite* proof is not the composite of the
-- transports, so restriction is only pseudo-functorial there.  The fix
-- is the same Yoneda move applied to the carrier: on the
-- transport-closed family
--
--     Cay X s = Σ[ s' ∈ S ] (s' Eq.≡ s) × X s'
--
-- the transports are proof-plumbing rather than computation, so
-- restriction becomes strictly functorial.  `Cay X` is not junk: the
-- second projection is an equivalence `Cay X s ≃ X s`, `εCay ∘ ηCay` on
-- the nose and `ηCay ∘ εCay` by `J`.
module _ {S : Type ℓS} where

  Cay : (S → Type ℓX) → S → Type (ℓ-max ℓS ℓX)
  Cay {ℓX = ℓX} X s = Σ[ s' ∈ S ] ((s' Eq.≡ s) × X s')

  module _ {X : S → Type ℓX} where

    ηCay : {s : S} → X s → Cay X s
    ηCay {s = s} z = s , Eq.refl , z

    εCay : {s : S} → Cay X s → X s
    εCay (s' , e , z) = Eq.transport X e z

    εηCay : {s : S} (z : X s) → εCay (ηCay z) ≡ z
    εηCay z = refl

    ηεCay : {s : S} (c : Cay X s) → ηCay (εCay c) ≡ c
    ηεCay (s' , Eq.refl , z) = refl

    -- the Yoneda-form coherences are natural, by `J`
    cayNat : {a b : S} (g : (s : S) → s Eq.≡ a → s Eq.≡ b) (c : Cay X a)
      → Eq.transport X (g (c .fst) (c .snd .fst)) (c .snd .snd)
        ≡ Eq.transport X (g a Eq.refl) (εCay c)
    cayNat g (s' , Eq.refl , z) = refl

  isSetCay : (isSetS : isSet S) {X : S → Type ℓX}
    → ((s : S) → isSet (X s)) → (s : S) → isSet (Cay X s)
  isSetCay isSetS isSetX s =
    isSetΣ isSetS (λ s' →
      isSet× (isProp→isSet (isPropEqS isSetS)) (isSetX s'))

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (F : SortedSigMapᶠ σ τ) where

  resOpsᶜ : (X : S → Type ℓX)
    → Ops {σ = τ} (Cay X) → Ops {σ = σ} (Cay X)
  resOpsᶜ X α o x =
    α (F .onOps o)
      (λ b → x (F .unArity o b) .fst
           , F .onSortOf o b _ (x (F .unArity o b) .snd .fst)
           , x (F .unArity o b) .snd .snd) .fst
    , F .onResult o _
        (α (F .onOps o)
          (λ b → x (F .unArity o b) .fst
               , F .onSortOf o b _ (x (F .unArity o b) .snd .fst)
               , x (F .unArity o b) .snd .snd) .snd .fst)
    , α (F .onOps o)
        (λ b → x (F .unArity o b) .fst
             , F .onSortOf o b _ (x (F .unArity o b) .snd .fst)
             , x (F .unArity o b) .snd .snd) .snd .snd

-- restriction is *strictly* functorial
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} (X : S → Type ℓX)
  (α : Ops {σ = σ} (Cay X)) where

  resOpsᶜ-id : resOpsᶜ idSortedSigMapᶠ X α ≡ α
  resOpsᶜ-id = refl

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {υ : SortedSig S ℓ3 ℓ3'} (F : SortedSigMapᶠ σ τ)
  (G : SortedSigMapᶠ τ υ) (X : S → Type ℓX)
  (α : Ops {σ = υ} (Cay X)) where

  resOpsᶜ-⋆ : resOpsᶜ (F ⋆SigMapᶠ G) X α ≡ resOpsᶜ F X (resOpsᶜ G X α)
  resOpsᶜ-⋆ = refl

-- ------------------------------------------------------------------
-- Theories displayed over signatures
-- ------------------------------------------------------------------

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (σeq : SortedEqns σ ℓ1'' ℓv) (τeq : SortedEqns τ ℓ2'' ℓw)
  (ℓX : Level) (F : SortedSigMapᶠ σ τ) where

  -- every σ-equation holds in the F-restriction of every τ-model on a
  -- transport-closed family
  PresEqnsᶜ : Type _
  PresEqnsᶜ = (X : S → hSet ℓX)
    (α : Ops {σ = τ} (Cay (λ s → ⟨ X s ⟩)))
    (sat : (e : τeq .eqns)
           (ρ : (v : τeq .vars e)
              → Cay (λ s → ⟨ X s ⟩) (τeq .varSort e v))
         → TmRec (Cay (λ s → ⟨ X s ⟩)) α ρ (τeq .lhs e)
           ≡ TmRec (Cay (λ s → ⟨ X s ⟩)) α ρ (τeq .rhs e))
    (e : σeq .eqns)
    (ρ : (v : σeq .vars e) → Cay (λ s → ⟨ X s ⟩) (σeq .varSort e v))
    → TmRec (Cay (λ s → ⟨ X s ⟩)) (resOpsᶜ F (λ s → ⟨ X s ⟩) α) ρ
        (σeq .lhs e)
      ≡ TmRec (Cay (λ s → ⟨ X s ⟩)) (resOpsᶜ F (λ s → ⟨ X s ⟩) α) ρ
          (σeq .rhs e)

  isPropPresEqnsᶜ : isSet S → isProp PresEqnsᶜ
  isPropPresEqnsᶜ isSetS =
    isPropΠ5 (λ X _ _ e _ →
      isSetCay isSetS (λ s → X s .snd) (σeq .eqnSort e) _ _)

module _ {S : Type ℓS} (isSetS : isSet S) (ℓ'' ℓv ℓX : Level) where

  SORTEDTHEORYᴰ : ∀ ℓ ℓ' → Categoryᴰ (SORTEDSIG isSetS ℓ ℓ') _ _
  SORTEDTHEORYᴰ ℓ ℓ' .Categoryᴰ.ob[_] σ = SortedEqns (σ .sig) ℓ'' ℓv
  SORTEDTHEORYᴰ ℓ ℓ' .Categoryᴰ.Hom[_][_,_] F σeq τeq =
    PresEqnsᶜ σeq τeq ℓX F
  SORTEDTHEORYᴰ ℓ ℓ' .Categoryᴰ.idᴰ X α sat = sat
  SORTEDTHEORYᴰ ℓ ℓ' .Categoryᴰ._⋆ᴰ_ {g = G} pF pG X α sat =
    pF X (resOpsᶜ G (λ s → ⟨ X s ⟩) α) (pG X α sat)
  SORTEDTHEORYᴰ ℓ ℓ' .Categoryᴰ.⋆IdLᴰ fᴰ = refl
  SORTEDTHEORYᴰ ℓ ℓ' .Categoryᴰ.⋆IdRᴰ fᴰ = refl
  SORTEDTHEORYᴰ ℓ ℓ' .Categoryᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ = refl
  SORTEDTHEORYᴰ ℓ ℓ' .Categoryᴰ.isSetHomᴰ {f = F} {xᴰ = σeq} {yᴰ = τeq} =
    isProp→isSet (isPropPresEqnsᶜ σeq τeq ℓX F isSetS)

  SORTEDTHEORY : ∀ ℓ ℓ' → Category _ _
  SORTEDTHEORY ℓ ℓ' = ∫C (SORTEDTHEORYᴰ ℓ ℓ')

-- ------------------------------------------------------------------
-- Back to honest models
-- ------------------------------------------------------------------
--
-- `Cay X ≃ X`, so nothing is lost by working over transport-closed
-- carriers: an interpretation on `X` lifts to one on `Cay X`, its
-- equations lift with it, and restriction on the lift is the lift of
-- restriction.
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} where

  liftOps : {X : S → Type ℓX} → Ops {σ = σ} X → Ops {σ = σ} (Cay X)
  liftOps α o x = ηCay (α o (λ a → εCay (x a)))

  TmRec-lift : {X : S → Type ℓX} (α : Ops {σ = σ} X)
    {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v))
    {s : S} (t : Tm σ V vs s)
    → TmRec (Cay X) (liftOps α) (λ v → ηCay (ρ v)) t
      ≡ ηCay (TmRec X α ρ t)
  TmRec-lift α ρ (var v) = refl
  TmRec-lift {X = X} α ρ (node o ts) =
    cong (λ z → ηCay {X = X} (α o z))
      (funExt (λ a → cong (εCay {X = X}) (TmRec-lift α ρ (ts a))))

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (F : SortedSigMapᶠ σ τ) where

  -- the honest restriction, read off the Yoneda-form coherences
  resOpsᶠ : (X : S → Type ℓX) → Ops {σ = τ} X → Ops {σ = σ} X
  resOpsᶠ X α o x =
    Eq.transport X (F .onResult o _ Eq.refl)
      (α (F .onOps o)
        (λ b → Eq.transport X (F .onSortOf o b _ Eq.refl)
                 (x (F .unArity o b))))

  resOpsᶠ≡resOps : (X : S → Type ℓX) (α : Ops {σ = τ} X)
    → resOpsᶠ X α ≡ resOps (toSortedSigMap F) X α
  resOpsᶠ≡resOps X α = funExt (λ o → funExt (λ x →
    cong (λ p → Eq.transport X p
                  (α (F .onOps o)
                    (λ b → Eq.transport X (F .onSortOf o b _ Eq.refl)
                             (x (F .unArity o b)))))
      (sym (Eq.eqToPath (Eq.sym-invol (F .onResult o _ Eq.refl))))))

  resOpsᶜ-lift : (X : S → Type ℓX) (α : Ops {σ = τ} X)
    → resOpsᶜ F X (liftOps α) ≡ liftOps (resOpsᶠ X α)
  resOpsᶜ-lift X α = funExt (λ o → funExt (λ x →
    sym (ηεCay _)
    ∙ cong (ηCay {X = X})
        (cong (Eq.transport X (F .onResult o _ Eq.refl))
          (cong (α (F .onOps o))
            (funExt (λ b →
              cayNat {X = X} (F .onSortOf o b)
                (x (F .unArity o b))))))))

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (σeq : SortedEqns σ ℓ1'' ℓv) (τeq : SortedEqns τ ℓ2'' ℓw)
  (ℓX : Level) (F : SortedSigMapᶠ σ τ) where

  -- a preservation proof in the strict sense gives one in the sense of
  -- `Morphism.agda`, so `resModOb`, `resModHom` and `resMod` all apply
  presᶜ→pres : PresEqnsᶜ σeq τeq ℓX F
    → PresEqns σeq τeq ℓX (toSortedSigMap F)
  presᶜ→pres pᶜ M e ρ =
    subst
      (λ β → TmRec X β ρ (σeq .lhs e) ≡ TmRec X β ρ (σeq .rhs e))
      (resOpsᶠ≡resOps F X α)
      (cong εCay
        (sym (TmRec-lift (resOpsᶠ F X α) ρ (σeq .lhs e))
         ∙ mid
         ∙ TmRec-lift (resOpsᶠ F X α) ρ (σeq .rhs e)))
    where
      X : S → Type ℓX
      X s = ⟨ M .fst s ⟩

      α : Ops {σ = τ} X
      α = M .snd .fst

      satLift : (e' : τeq .eqns)
        (ρ' : (v : τeq .vars e') → Cay X (τeq .varSort e' v))
        → TmRec (Cay X) (liftOps α) ρ' (τeq .lhs e')
          ≡ TmRec (Cay X) (liftOps α) ρ' (τeq .rhs e')
      satLift e' ρ' =
        cong (λ r → TmRec (Cay X) (liftOps α) r (τeq .lhs e'))
          (sym (funExt (λ v → ηεCay (ρ' v))))
        ∙ TmRec-lift α (λ v → εCay (ρ' v)) (τeq .lhs e')
        ∙ cong (ηCay {X = X}) (M .snd .snd e' (λ v → εCay (ρ' v)))
        ∙ sym (TmRec-lift α (λ v → εCay (ρ' v)) (τeq .rhs e'))
        ∙ cong (λ r → TmRec (Cay X) (liftOps α) r (τeq .rhs e'))
            (funExt (λ v → ηεCay (ρ' v)))

      mid : TmRec (Cay X) (liftOps (resOpsᶠ F X α)) (λ v → ηCay (ρ v))
              (σeq .lhs e)
            ≡ TmRec (Cay X) (liftOps (resOpsᶠ F X α)) (λ v → ηCay (ρ v))
                (σeq .rhs e)
      mid =
        subst
          (λ γ → TmRec (Cay X) γ (λ v → ηCay (ρ v)) (σeq .lhs e)
               ≡ TmRec (Cay X) γ (λ v → ηCay (ρ v)) (σeq .rhs e))
          (resOpsᶜ-lift F X α)
          (pᶜ (M .fst) (liftOps α) satLift e (λ v → ηCay (ρ v)))

-- ------------------------------------------------------------------
-- Reindexing of models
-- ------------------------------------------------------------------
--
-- The sorted analogue of `Theories.MODReindexᴰ`.  It is *vertical*:
-- restriction changes neither the carrier family nor the underlying
-- function of a homomorphism, so it lies over `Id` on `FAM S ℓX`.
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (σeq : SortedEqns σ ℓ1'' ℓv) (τeq : SortedEqns τ ℓ2'' ℓw)
  (ℓX : Level) (F : SortedSigMap σ τ)
  (pres : PresEqns σeq τeq ℓX F) where

  private
    module Mσ = Categoryᴰ (MODᴰ σeq ℓX)

    isPropHomᴰ : {X Y : Category.ob (FAM S ℓX)}
      (f : Category.Hom[_,_] (FAM S ℓX) X Y)
      (Mᴰ : Mσ.ob[ X ]) (Nᴰ : Mσ.ob[ Y ])
      → isProp (Mσ.Hom[ f ][ Mᴰ , Nᴰ ])
    isPropHomᴰ {Y = Y} f Mᴰ Nᴰ =
      isPropΣ (isPropΠ4 (λ _ _ _ _ → Y _ .snd _ _)) (λ _ → isPropUnit*)

  MODReindexᴰ : Functorⱽ (MODᴰ τeq ℓX) (MODᴰ σeq ℓX)
  MODReindexᴰ .Functorᴰ.F-obᴰ {x = X} Mᴰ =
    resOps F (λ s → ⟨ X s ⟩) (Mᴰ .fst) , pres (X , Mᴰ)
  MODReindexᴰ .Functorᴰ.F-homᴰ {f = f} {xᴰ = Mᴰ} {yᴰ = Nᴰ} ϕ =
    resHomCond F f (Mᴰ .fst) (Nᴰ .fst) (ϕ .fst) , tt*
  MODReindexᴰ .Functorᴰ.F-idᴰ = isPropHomᴰ _ _ _ _ _
  MODReindexᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ = isPropHomᴰ _ _ _ _ _

-- ------------------------------------------------------------------
-- The laws, verbatim
-- ------------------------------------------------------------------

module _ {S : Type ℓS} (isSetS : isSet S) (ℓ ℓ' : Level) where
  private module Sig = Category (SORTEDSIG isSetS ℓ ℓ')

  SORTEDSIG-⋆IdL : {x y : Sig.ob} (f : Sig.Hom[ x , y ])
    → Sig._⋆_ {x = x} {y = x} {z = y} (Sig.id {x = x}) f ≡ f
  SORTEDSIG-⋆IdL f = refl

  SORTEDSIG-⋆IdR : {x y : Sig.ob} (f : Sig.Hom[ x , y ])
    → Sig._⋆_ {x = x} {y = y} {z = y} f (Sig.id {x = y}) ≡ f
  SORTEDSIG-⋆IdR f = refl

  SORTEDSIG-⋆Assoc : {w x y z : Sig.ob}
    (f : Sig.Hom[ w , x ]) (g : Sig.Hom[ x , y ]) (h : Sig.Hom[ y , z ])
    → Sig._⋆_ {x = w} {y = y} {z = z} (Sig._⋆_ {x = w} {y = x} {z = y} f g) h
      ≡ Sig._⋆_ {x = w} {y = x} {z = z} f
          (Sig._⋆_ {x = x} {y = y} {z = z} g h)
  SORTEDSIG-⋆Assoc f g h = refl

module _ {S : Type ℓS} (isSetS : isSet S) (ℓ'' ℓv ℓX ℓ ℓ' : Level) where
  private module Th = Category (SORTEDTHEORY isSetS ℓ'' ℓv ℓX ℓ ℓ')

  SORTEDTHEORY-⋆IdL : {x y : Th.ob} (f : Th.Hom[ x , y ])
    → Th._⋆_ {x = x} {y = x} {z = y} (Th.id {x = x}) f ≡ f
  SORTEDTHEORY-⋆IdL f = refl

  SORTEDTHEORY-⋆IdR : {x y : Th.ob} (f : Th.Hom[ x , y ])
    → Th._⋆_ {x = x} {y = y} {z = y} f (Th.id {x = y}) ≡ f
  SORTEDTHEORY-⋆IdR f = refl

  SORTEDTHEORY-⋆Assoc : {w x y z : Th.ob}
    (f : Th.Hom[ w , x ]) (g : Th.Hom[ x , y ]) (h : Th.Hom[ y , z ])
    → Th._⋆_ {x = w} {y = y} {z = z} (Th._⋆_ {x = w} {y = x} {z = y} f g) h
      ≡ Th._⋆_ {x = w} {y = x} {z = z} f
          (Th._⋆_ {x = x} {y = y} {z = z} g h)
  SORTEDTHEORY-⋆Assoc f g h = refl

-- ------------------------------------------------------------------
-- Letting the sort set vary: why it is not here
-- ------------------------------------------------------------------
--
-- `ChangeOfSorts` supplies `reSig`, which is *strictly* functorial
-- (`reSigId` and `reSigComp` are both `refl`), so the obvious sort-
-- varying category has objects `(S , σ)` and morphisms `(h , F)` with
-- `h : S → S'` and `F : SortedSigMapᶠ (reSig h σ) τ`.  Composition has
-- to reindex `F` along `g : S' → S''`, and that is where strictness
-- dies: reindexing a coherence means applying `Eq.ap g` to it, and
--
--     Eq.ap g (p Eq.∙ q)  vs  Eq.ap g p Eq.∙ Eq.ap g q
--
-- differ -- `Eq.ap-∙` recurses on `p`, so this is not `refl` -- while
-- the Yoneda form of this file is not stable under postcomposition
-- with `g` at all: from
--
--     (t : S') → t Eq.≡ h a → t Eq.≡ b
--
-- one cannot produce `(u : S'') → u Eq.≡ g (h a) → u Eq.≡ g b` without
-- first extracting the underlying equation.  The repair is to quantify
-- the coherence over *all* later reindexings,
--
--     (S'' : hSet ℓS) (k : S' → ⟨ S'' ⟩) (u : ⟨ S'' ⟩)
--       → u Eq.≡ k (h a) → u Eq.≡ k b ,
--
-- for which composition is again plumbing (`k ∘ g` reassociates on the
-- nose) and all three laws are `refl`.  But that type is only a
-- retract of the equation, not equivalent to it without parametricity,
-- so such a morphism carries junk that no construction can eliminate.
-- The fixed-sort category above has no junk, so the sort-varying
-- version is deliberately left out rather than shipped with either
-- propositional laws or junk morphisms.
