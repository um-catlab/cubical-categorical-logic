{-# OPTIONS --lossy-unification #-}
-- The tensor of two sorted theories.
--
-- `σ ⊗ τ` is `σ ⊕ τ` with the extra equations saying that every
-- operation of σ commutes with every operation of τ.  Sortedness cuts
-- that family down, and by exactly how much is the content of this
-- file.  Write the interchange law for `f : σ .ops`, `g : τ .ops` on an
-- array `x : arities f × arities g → _`:
--
--     f (λ a → g (λ b → x a b))  ≡  g (λ b → f (λ a → x a b))
--
-- For the left-hand side to typecheck, `x a b` sits at `sortOf g b` and
-- `resultSort g` must be `sortOf f a`, for every `a`.  For the
-- right-hand side, `x a b` sits at `sortOf f a` and `resultSort f` must
-- be `sortOf g b`, for every `b`.  For the two sides to be an equation
-- at all, `resultSort f` must equal `resultSort g`.  Together: there is
-- one sort `s` with
--
--     resultSort f = s,  sortOf f a = s,  resultSort g = s,  sortOf g b = s
--
-- i.e. *both operations are homogeneous at a common sort*.  No other
-- pair can be asked to commute -- there is no array to state the law
-- on.  So the commuting family is indexed by `CommPair`, a sort
-- together with a `HomogOp` of each signature at it, rather than by
-- `σ .ops × τ .ops`.
--
-- Which pairs this excludes is easy to say.  Composition in the theory
-- of categories, `hom a b × hom b c → hom a c` at sort `(a , c)`, is
-- homogeneous exactly when `a = b = c`, so it can be asked to commute
-- with a τ-operation only at the endomorphism sorts `(a , a)` -- and at
-- the sorts `(a , b)` with `a ≠ b` it cannot be asked to commute with
-- anything at all, itself included, because there is no rectangular
-- array of the right sorts to state the law on.  That is a statement
-- about interchange, not about this encoding.
--
-- The single-sorted `⊗` is the special case `S = Unit`: `Unit`'s η
-- makes every coherence trivial, every operation is homogeneous at the
-- unique sort, and `CommPair σ τ ≅ σ .ops × τ .ops` again.  That is
-- `CommPairUnitIso` at the end of this file.
module Cubical.Algebra.Theory.Sorted.Tensor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit

open import Cubical.Algebra.Theory.Sorted
open import Cubical.Algebra.Theory.Sorted.Constructions
open import Cubical.Algebra.Theory.Sorted.Theories
open import Cubical.Algebra.Theory.Sorted.Coproduct

private
  variable
    ℓS ℓ ℓ' ℓ1 ℓ2 ℓ3 ℓ'' ℓ1'' ℓ2'' ℓ3'' ℓv ℓw ℓX : Level

open SortedSig
open SortedEqns

-- ------------------------------------------------------------------
-- Homogeneous operations
-- ------------------------------------------------------------------

record HomogOp {S : Type ℓS} (υ : SortedSig S ℓ ℓ') (s : S)
  : Type (ℓ-max ℓS (ℓ-max ℓ ℓ')) where
  field
    hOp : υ .ops
    hRes : υ .resultSort hOp Eq.≡ s
    hArg : (a : υ .arities hOp) → υ .sortOf hOp a Eq.≡ s

open HomogOp

-- the two summands of `σ ⊕Sig τ` inherit homogeneity on the nose
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ'} {τ : SortedSig S ℓ2 ℓ'}
  {s : S} where

  inlHomog : HomogOp σ s → HomogOp (σ ⊕Sig τ) s
  inlHomog h .hOp = inl (h .hOp)
  inlHomog h .hRes = h .hRes
  inlHomog h .hArg = h .hArg

  inrHomog : HomogOp τ s → HomogOp (σ ⊕Sig τ) s
  inrHomog h .hOp = inr (h .hOp)
  inrHomog h .hRes = h .hRes
  inrHomog h .hArg = h .hArg

-- ------------------------------------------------------------------
-- Terms and interpretations at a single sort
-- ------------------------------------------------------------------

module _ {S : Type ℓS} {X : S → Type ℓX} where

  atSortX : {s s' : S} → s Eq.≡ s' → X s → X s'
  atSortX e = Eq.transport X e

module _ {S : Type ℓS} {υ : SortedSig S ℓ ℓ'}
  {V : Type ℓv} {vs : V → S} where

  atSortTm : {s s' : S} → s Eq.≡ s' → Tm υ V vs s → Tm υ V vs s'
  atSortTm Eq.refl t = t

  -- a homogeneous operation applied to arguments all at its sort
  homNodeTm : {s : S} (h : HomogOp υ s)
    → ((a : υ .arities (h .hOp)) → Tm υ V vs s) → Tm υ V vs s
  homNodeTm h ts =
    atSortTm (h .hRes)
      (node (h .hOp) (λ a → atSortTm (Eq.sym (h .hArg a)) (ts a)))

module _ {S : Type ℓS} {υ : SortedSig S ℓ ℓ'} {X : S → Type ℓX}
  (α : Ops {σ = υ} X) where

  homOps : {s : S} (h : HomogOp υ s)
    → ((a : υ .arities (h .hOp)) → X s) → X s
  homOps h x =
    atSortX (h .hRes)
      (α (h .hOp) (λ a → atSortX (Eq.sym (h .hArg a)) (x a)))

module _ {S : Type ℓS} {υ : SortedSig S ℓ ℓ'} {X : S → Type ℓX}
  (α : Ops {σ = υ} X) {V : Type ℓv} {vs : V → S}
  (ρ : (v : V) → X (vs v)) where

  TmRec-atSortTm : {s s' : S} (e : s Eq.≡ s') (t : Tm υ V vs s)
    → TmRec X α ρ (atSortTm e t) ≡ atSortX e (TmRec X α ρ t)
  TmRec-atSortTm Eq.refl t = refl

  TmRec-homNodeTm : {s : S} (h : HomogOp υ s)
    (ts : (a : υ .arities (h .hOp)) → Tm υ V vs s)
    → TmRec X α ρ (homNodeTm h ts)
      ≡ homOps α h (λ a → TmRec X α ρ (ts a))
  TmRec-homNodeTm h ts =
      TmRec-atSortTm (h .hRes) _
    ∙ cong (atSortX (h .hRes))
        (cong (α (h .hOp))
          (funExt (λ a → TmRec-atSortTm (Eq.sym (h .hArg a)) (ts a))))

-- ------------------------------------------------------------------
-- The commuting pairs, and the tensor's equations
-- ------------------------------------------------------------------

module _ {S : Type ℓS} (σ : SortedSig S ℓ1 ℓ') (τ : SortedSig S ℓ2 ℓ')
  where

  -- the pairs of operations that *can* be asked to commute: a sort,
  -- and an operation of each signature homogeneous at it
  CommPair : Type (ℓ-max ℓS (ℓ-max ℓ1 (ℓ-max ℓ2 ℓ')))
  CommPair = Σ[ s ∈ S ] (HomogOp σ s × HomogOp τ s)

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ'} {τ : SortedSig S ℓ2 ℓ'}
  (ℓw : Level) where

  commVars : CommPair σ τ → Type (ℓ-max ℓ' ℓw)
  commVars (s , hf , hg) =
    Lift ℓw (σ .arities (hf .hOp) × τ .arities (hg .hOp))

  commLhs : (c : CommPair σ τ)
    → Tm (σ ⊕Sig τ) (commVars c) (λ _ → c .fst) (c .fst)
  commLhs (s , hf , hg) =
    homNodeTm (inlHomog hf)
      (λ a → homNodeTm (inrHomog hg) (λ b → var (lift (a , b))))

  commRhs : (c : CommPair σ τ)
    → Tm (σ ⊕Sig τ) (commVars c) (λ _ → c .fst) (c .fst)
  commRhs (s , hf , hg) =
    homNodeTm (inrHomog hg)
      (λ b → homNodeTm (inlHomog hf) (λ a → var (lift (a , b))))

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ'} {τ : SortedSig S ℓ2 ℓ'}
  (ℓw : Level) (σeq : SortedEqns σ ℓ1'' (ℓ-max ℓ' ℓw))
  (τeq : SortedEqns τ ℓ2'' (ℓ-max ℓ' ℓw)) where

  ⊗Eqns : SortedEqns (σ ⊕Sig τ)
    (ℓ-max (ℓ-max ℓ1'' ℓ2'') (ℓ-max ℓS (ℓ-max ℓ1 (ℓ-max ℓ2 ℓ'))))
    (ℓ-max ℓ' ℓw)
  ⊗Eqns .eqns = σeq .eqns ⊎ (τeq .eqns ⊎ CommPair σ τ)
  ⊗Eqns .eqnSort (inl e) = σeq .eqnSort e
  ⊗Eqns .eqnSort (inr (inl e)) = τeq .eqnSort e
  ⊗Eqns .eqnSort (inr (inr c)) = c .fst
  ⊗Eqns .vars (inl e) = σeq .vars e
  ⊗Eqns .vars (inr (inl e)) = τeq .vars e
  ⊗Eqns .vars (inr (inr c)) = commVars ℓw c
  ⊗Eqns .varSort (inl e) = σeq .varSort e
  ⊗Eqns .varSort (inr (inl e)) = τeq .varSort e
  ⊗Eqns .varSort (inr (inr c)) _ = c .fst
  ⊗Eqns .lhs (inl e) = inlTm σ τ (σeq .lhs e)
  ⊗Eqns .lhs (inr (inl e)) = inrTm σ τ (τeq .lhs e)
  ⊗Eqns .lhs (inr (inr c)) = commLhs ℓw c
  ⊗Eqns .rhs (inl e) = inlTm σ τ (σeq .rhs e)
  ⊗Eqns .rhs (inr (inl e)) = inrTm σ τ (τeq .rhs e)
  ⊗Eqns .rhs (inr (inr c)) = commRhs ℓw c

  -- the tensor receives both summands, and receives the coproduct.
  -- `resOpsᶜ (inlSigMapᶠ σ τ) Y α` is `resl σ τ Y α` and
  -- `resOpsᶜ idSortedSigMapᶠ Y α` is `α`, both definitionally, so these
  -- are the same three-step arguments as for `_⊕Eqns_`.
  module _ (ℓX : Level) where

    pInl⊗ᶜ : PresEqnsᶜ σeq ⊗Eqns ℓX (inlSigMapᶠ σ τ)
    pInl⊗ᶜ X α sat e ρ =
        sym (TmRec-inl σ τ (Cay (λ s → ⟨ X s ⟩)) α ρ (σeq .lhs e))
      ∙ sat (inl e) ρ
      ∙ TmRec-inl σ τ (Cay (λ s → ⟨ X s ⟩)) α ρ (σeq .rhs e)

    pInr⊗ᶜ : PresEqnsᶜ τeq ⊗Eqns ℓX (inrSigMapᶠ σ τ)
    pInr⊗ᶜ X α sat e ρ =
        sym (TmRec-inr σ τ (Cay (λ s → ⟨ X s ⟩)) α ρ (τeq .lhs e))
      ∙ sat (inr (inl e)) ρ
      ∙ TmRec-inr σ τ (Cay (λ s → ⟨ X s ⟩)) α ρ (τeq .rhs e)

    -- the quotient map `σ ⊕ τ → σ ⊗ τ`, over the identity signature map
    ⊕→⊗ᶜ : PresEqnsᶜ (σeq ⊕Eqns τeq) ⊗Eqns ℓX idSortedSigMapᶠ
    ⊕→⊗ᶜ X α sat (inl e) ρ = sat (inl e) ρ
    ⊕→⊗ᶜ X α sat (inr e) ρ = sat (inr (inl e)) ρ

-- ------------------------------------------------------------------
-- Models of the tensor
-- ------------------------------------------------------------------
--
-- A model of `σ ⊗ τ` on `X` is a model of each of σ and τ on `X` whose
-- homogeneous operations commute.  `homOps α hf` is `homOps γ
-- (inlHomog hf)` definitionally, so nothing has to be transported
-- between the two views.
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ'} {τ : SortedSig S ℓ2 ℓ'}
  (ℓw : Level) (σeq : SortedEqns σ ℓ1'' (ℓ-max ℓ' ℓw))
  (τeq : SortedEqns τ ℓ2'' (ℓ-max ℓ' ℓw)) (X : S → hSet ℓX) where

  private
    Y : S → Type ℓX
    Y s = ⟨ X s ⟩

  Commutes : Ops {σ = σ} Y → Ops {σ = τ} Y
    → Type (ℓ-max ℓS (ℓ-max ℓ1 (ℓ-max ℓ2 (ℓ-max ℓ' ℓX))))
  Commutes α β = (s : S) (hf : HomogOp σ s) (hg : HomogOp τ s)
    (x : σ .arities (hf .hOp) → τ .arities (hg .hOp) → Y s)
    → homOps α hf (λ a → homOps β hg (λ b → x a b))
      ≡ homOps β hg (λ b → homOps α hf (λ a → x a b))

  isPropCommutes : (α : Ops {σ = σ} Y) (β : Ops {σ = τ} Y)
    → isProp (Commutes α β)
  isPropCommutes α β =
    isPropΠ4 (λ s _ _ _ → X s .snd _ _)

  ⊗Model : Type _
  ⊗Model = Σ[ MN ∈ (ModOn σeq X × ModOn τeq X) ]
    Commutes (MN .fst .fst) (MN .snd .fst)

  -- reading the commutation equation off a `σ ⊕Sig τ`-interpretation
  module _ (γ : Ops {σ = σ ⊕Sig τ} Y) {s : S}
    (hf : HomogOp σ s) (hg : HomogOp τ s)
    (x : σ .arities (hf .hOp) → τ .arities (hg .hOp) → Y s) where

    private
      ρ : Lift ℓw (σ .arities (hf .hOp) × τ .arities (hg .hOp)) → Y s
      ρ p = x (p .lower .fst) (p .lower .snd)

    commTmRecL :
      TmRec Y γ ρ (commLhs ℓw (s , hf , hg))
      ≡ homOps γ (inlHomog hf) (λ a → homOps γ (inrHomog hg) (x a))
    commTmRecL =
        TmRec-homNodeTm γ ρ (inlHomog hf) _
      ∙ cong (homOps γ (inlHomog hf))
          (funExt (λ a → TmRec-homNodeTm γ ρ (inrHomog hg) _))

    commTmRecR :
      TmRec Y γ ρ (commRhs ℓw (s , hf , hg))
      ≡ homOps γ (inrHomog hg) (λ b → homOps γ (inlHomog hf) (λ a → x a b))
    commTmRecR =
        TmRec-homNodeTm γ ρ (inrHomog hg) _
      ∙ cong (homOps γ (inrHomog hg))
          (funExt (λ b → TmRec-homNodeTm γ ρ (inlHomog hf) _))

  ⊗ModIso : Iso (ModOn (⊗Eqns ℓw σeq τeq) X) ⊗Model
  ⊗ModIso .Iso.fun M =
      ( (resl σ τ Y γ , λ e ρ →
            sym (TmRec-inl σ τ Y γ ρ (σeq .lhs e))
          ∙ M .snd (inl e) ρ
          ∙ TmRec-inl σ τ Y γ ρ (σeq .rhs e))
      , (resr σ τ Y γ , λ e ρ →
            sym (TmRec-inr σ τ Y γ ρ (τeq .lhs e))
          ∙ M .snd (inr (inl e)) ρ
          ∙ TmRec-inr σ τ Y γ ρ (τeq .rhs e)) )
    , λ s hf hg x →
          sym (commTmRecL γ hf hg x)
        ∙ M .snd (inr (inr (s , hf , hg)))
            (λ p → x (p .lower .fst) (p .lower .snd))
        ∙ commTmRecR γ hf hg x
    where γ = M .fst
  ⊗ModIso .Iso.inv ((M , N) , comm) = γ , sat
    where
      γ : Ops {σ = σ ⊕Sig τ} Y
      γ = ⊕Ops σeq τeq X (M .fst) (N .fst)

      sat : (e : (⊗Eqns ℓw σeq τeq) .eqns)
        (ρ : (v : (⊗Eqns ℓw σeq τeq) .vars e)
           → Y ((⊗Eqns ℓw σeq τeq) .varSort e v))
        → TmRec Y γ ρ ((⊗Eqns ℓw σeq τeq) .lhs e)
          ≡ TmRec Y γ ρ ((⊗Eqns ℓw σeq τeq) .rhs e)
      sat (inl e) ρ =
          TmRec-inl σ τ Y γ ρ (σeq .lhs e)
        ∙ M .snd e ρ
        ∙ sym (TmRec-inl σ τ Y γ ρ (σeq .rhs e))
      sat (inr (inl e)) ρ =
          TmRec-inr σ τ Y γ ρ (τeq .lhs e)
        ∙ N .snd e ρ
        ∙ sym (TmRec-inr σ τ Y γ ρ (τeq .rhs e))
      sat (inr (inr (s , hf , hg))) ρ =
          commTmRecL γ hf hg x
        ∙ comm s hf hg x
        ∙ sym (commTmRecR γ hf hg x)
        where x = λ a b → ρ (lift (a , b))
  ⊗ModIso .Iso.sec ((M , N) , comm) =
    Σ≡Prop (λ _ → isPropCommutes _ _)
      (ΣPathP (ModOn≡ σeq X refl , ModOn≡ τeq X refl))
  ⊗ModIso .Iso.ret M =
    ModOn≡ (⊗Eqns ℓw σeq τeq) X
      (funExt (λ { (inl o) → refl ; (inr o) → refl }))

  -- as for the coproduct, the round trips are `refl` on the
  -- operations and only move the (propositional) equation and
  -- commutation components
  ⊗ModIso-secOpsL : (M : ModOn σeq X) (N : ModOn τeq X)
    (c : Commutes (M .fst) (N .fst))
    → ⊗ModIso .Iso.fun (⊗ModIso .Iso.inv ((M , N) , c)) .fst .fst .fst
      ≡ M .fst
  ⊗ModIso-secOpsL M N c = refl

  ⊗ModIso-secOpsR : (M : ModOn σeq X) (N : ModOn τeq X)
    (c : Commutes (M .fst) (N .fst))
    → ⊗ModIso .Iso.fun (⊗ModIso .Iso.inv ((M , N) , c)) .fst .snd .fst
      ≡ N .fst
  ⊗ModIso-secOpsR M N c = refl

  ⊗ModIso-retOpsL : (M : ModOn (⊗Eqns ℓw σeq τeq) X) (o : σ .ops)
    → ⊗ModIso .Iso.inv (⊗ModIso .Iso.fun M) .fst (inl o) ≡ M .fst (inl o)
  ⊗ModIso-retOpsL M o = refl

  ⊗ModIso-retOpsR : (M : ModOn (⊗Eqns ℓw σeq τeq) X) (o : τ .ops)
    → ⊗ModIso .Iso.inv (⊗ModIso .Iso.fun M) .fst (inr o) ≡ M .fst (inr o)
  ⊗ModIso-retOpsR M o = refl

-- ------------------------------------------------------------------
-- The single-sorted tensor is the case `S = Unit`
-- ------------------------------------------------------------------
--
-- Confirmation that `CommPair` really is the right restriction and not
-- an over-cautious one: when there is only one sort, `Unit`'s η makes
-- every sort coherence a proof of `tt Eq.≡ tt`, so `HomogOp υ tt` is
-- `υ .ops` and `CommPair σ τ` is `σ .ops × τ .ops` -- the single-sorted
-- `⊗Eqns`, on the nose.
module _ {υ : SortedSig Unit ℓ ℓ'} where

  HomogOpUnitIso : Iso (HomogOp υ tt) (υ .ops)
  HomogOpUnitIso .Iso.fun h = h .hOp
  HomogOpUnitIso .Iso.inv o .hOp = o
  HomogOpUnitIso .Iso.inv o .hRes = Eq.refl
  HomogOpUnitIso .Iso.inv o .hArg _ = Eq.refl
  HomogOpUnitIso .Iso.sec o = refl
  HomogOpUnitIso .Iso.ret h i .hOp = h .hOp
  HomogOpUnitIso .Iso.ret h i .hRes =
    isPropEqS isSetUnit Eq.refl (h .hRes) i
  HomogOpUnitIso .Iso.ret h i .hArg a =
    isPropEqS isSetUnit Eq.refl (h .hArg a) i

module _ {σ : SortedSig Unit ℓ1 ℓ'} {τ : SortedSig Unit ℓ2 ℓ'} where

  CommPairUnitIso : Iso (CommPair σ τ) (σ .ops × τ .ops)
  CommPairUnitIso .Iso.fun (tt , hf , hg) =
    HomogOpUnitIso .Iso.fun hf , HomogOpUnitIso .Iso.fun hg
  CommPairUnitIso .Iso.inv (f , g) =
    tt , HomogOpUnitIso .Iso.inv f , HomogOpUnitIso .Iso.inv g
  CommPairUnitIso .Iso.sec (f , g) = refl
  CommPairUnitIso .Iso.ret (tt , hf , hg) =
    ΣPathP (refl , ΣPathP ( HomogOpUnitIso .Iso.ret hf
                          , HomogOpUnitIso .Iso.ret hg ))
