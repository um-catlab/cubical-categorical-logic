{-# OPTIONS --lossy-unification #-}
-- The universal property of `_⊕Sig_`/`_⊕Eqns_`.
module Cubical.Algebra.Theory.Sorted.Coproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr; isSet⊎)

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Limits.BinCoproduct

open import Cubical.Algebra.Theory.Sorted
open import Cubical.Algebra.Theory.Sorted.Constructions
open import Cubical.Algebra.Theory.Sorted.Theories

private
  variable
    ℓS ℓ ℓ' ℓ1 ℓ2 ℓ3 ℓ'' ℓ1'' ℓ2'' ℓ3'' ℓv ℓX : Level

open SortedSig
open SortedEqns
open SortedSetSig
open SortedSigMapᶠ

-- ------------------------------------------------------------------
-- The injections
-- ------------------------------------------------------------------
--
-- `(σ ⊕Sig τ) .arities (inl o)`, `.sortOf (inl o)` and `.resultSort
-- (inl o)` are the σ-ones on the nose, so both Yoneda-form coherences
-- are the identity function: the injections are `idSortedSigMapᶠ`
-- with `inl`/`inr` glued on.
module _ {S : Type ℓS} (σ : SortedSig S ℓ1 ℓ') (τ : SortedSig S ℓ2 ℓ')
  where

  inlSigMapᶠ : SortedSigMapᶠ σ (σ ⊕Sig τ)
  inlSigMapᶠ .onOps = inl
  inlSigMapᶠ .unArity o a = a
  inlSigMapᶠ .onSortOf o a s e = e
  inlSigMapᶠ .onResult o s e = e

  inrSigMapᶠ : SortedSigMapᶠ τ (σ ⊕Sig τ)
  inrSigMapᶠ .onOps = inr
  inrSigMapᶠ .unArity o a = a
  inrSigMapᶠ .onSortOf o a s e = e
  inrSigMapᶠ .onResult o s e = e

-- ------------------------------------------------------------------
-- The cotupling
-- ------------------------------------------------------------------

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ'} {τ : SortedSig S ℓ2 ℓ'}
  {υ : SortedSig S ℓ3 ℓ'}
  (F : SortedSigMapᶠ σ υ) (G : SortedSigMapᶠ τ υ) where

  [_,_]SigMapᶠ : SortedSigMapᶠ (σ ⊕Sig τ) υ
  [_,_]SigMapᶠ .onOps (inl o) = F .onOps o
  [_,_]SigMapᶠ .onOps (inr o) = G .onOps o
  [_,_]SigMapᶠ .unArity (inl o) a = F .unArity o a
  [_,_]SigMapᶠ .unArity (inr o) a = G .unArity o a
  [_,_]SigMapᶠ .onSortOf (inl o) a s e = F .onSortOf o a s e
  [_,_]SigMapᶠ .onSortOf (inr o) a s e = G .onSortOf o a s e
  [_,_]SigMapᶠ .onResult (inl o) s e = F .onResult o s e
  [_,_]SigMapᶠ .onResult (inr o) s e = G .onResult o s e

  -- both β laws are `refl`: composing with an injection is plugging
  -- `inl`/`inr` into the case split, and the coherence components
  -- compose as identity functions.
  ⊕SigMapᶠβl : (inlSigMapᶠ σ τ ⋆SigMapᶠ [_,_]SigMapᶠ) ≡ F
  ⊕SigMapᶠβl = refl

  ⊕SigMapᶠβr : (inrSigMapᶠ σ τ ⋆SigMapᶠ [_,_]SigMapᶠ) ≡ G
  ⊕SigMapᶠβr = refl

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ'} {τ : SortedSig S ℓ2 ℓ'}
  {υ : SortedSig S ℓ3 ℓ'} where

  -- η: the only failure of `refl` is the missing η for `_⊎_`, so the
  -- path is a case split that is `refl` in each branch.
  ⊕SigMapᶠη : (H : SortedSigMapᶠ (σ ⊕Sig τ) υ)
    → [ inlSigMapᶠ σ τ ⋆SigMapᶠ H , inrSigMapᶠ σ τ ⋆SigMapᶠ H ]SigMapᶠ ≡ H
  ⊕SigMapᶠη H i .onOps (inl o) = H .onOps (inl o)
  ⊕SigMapᶠη H i .onOps (inr o) = H .onOps (inr o)
  ⊕SigMapᶠη H i .unArity (inl o) a = H .unArity (inl o) a
  ⊕SigMapᶠη H i .unArity (inr o) a = H .unArity (inr o) a
  ⊕SigMapᶠη H i .onSortOf (inl o) a s e = H .onSortOf (inl o) a s e
  ⊕SigMapᶠη H i .onSortOf (inr o) a s e = H .onSortOf (inr o) a s e
  ⊕SigMapᶠη H i .onResult (inl o) s e = H .onResult (inl o) s e
  ⊕SigMapᶠη H i .onResult (inr o) s e = H .onResult (inr o) s e

  ⊕SigMapᶠIso : Iso (SortedSigMapᶠ (σ ⊕Sig τ) υ)
                    (SortedSigMapᶠ σ υ × SortedSigMapᶠ τ υ)
  ⊕SigMapᶠIso .Iso.fun H =
    (inlSigMapᶠ σ τ ⋆SigMapᶠ H) , (inrSigMapᶠ σ τ ⋆SigMapᶠ H)
  ⊕SigMapᶠIso .Iso.inv (F , G) = [ F , G ]SigMapᶠ
  ⊕SigMapᶠIso .Iso.sec _ = refl
  ⊕SigMapᶠIso .Iso.ret = ⊕SigMapᶠη

-- ------------------------------------------------------------------
-- `σ ⊕Sig τ` is the coproduct in `SORTEDSIG`
-- ------------------------------------------------------------------

module _ {S : Type ℓS} (isSetS : isSet S) (σ τ : SortedSetSig S ℓ ℓ')
  where

  _⊕SortedSetSig_ : SortedSetSig S ℓ ℓ'
  _⊕SortedSetSig_ .sig = σ .sig ⊕Sig τ .sig
  _⊕SortedSetSig_ .isSetOps = isSet⊎ (σ .isSetOps) (τ .isSetOps)
  _⊕SortedSetSig_ .isSetArities (inl o) = σ .isSetArities o
  _⊕SortedSetSig_ .isSetArities (inr o) = τ .isSetArities o

  SORTEDSIGBinCoproduct : BinCoproduct (SORTEDSIG isSetS ℓ ℓ') σ τ
  SORTEDSIGBinCoproduct .BinCoproduct.binCoprodOb = _⊕SortedSetSig_
  SORTEDSIGBinCoproduct .BinCoproduct.binCoprodInj₁ =
    inlSigMapᶠ (σ .sig) (τ .sig)
  SORTEDSIGBinCoproduct .BinCoproduct.binCoprodInj₂ =
    inrSigMapᶠ (σ .sig) (τ .sig)
  SORTEDSIGBinCoproduct .BinCoproduct.univProp F G .fst =
    [ F , G ]SigMapᶠ , refl , refl
  SORTEDSIGBinCoproduct .BinCoproduct.univProp {z = υ} F G .snd
    (H , p , q) =
    Σ≡Prop
      (λ _ → isProp×
        (isSetSortedSigMapᶠ isSetS (υ .isSetOps) (σ .isSetArities) _ _)
        (isSetSortedSigMapᶠ isSetS (υ .isSetOps) (τ .isSetArities) _ _))
      (cong₂ (λ F' G' → [ F' , G' ]SigMapᶠ) (sym p) (sym q)
       ∙ ⊕SigMapᶠη H)

-- ------------------------------------------------------------------
-- The injections preserve equations
-- ------------------------------------------------------------------
--
-- `resOpsᶜ (inlSigMapᶠ σ τ) X α` is `resl σ τ X α` *definitionally*:
-- the coherence components of the injection are identities, and the
-- `Cay`-triple that `resOpsᶜ` rebuilds is the η-expansion of the one it
-- was given, which Σ-types have on the nose.  So all four preservation
-- proofs below are the ones `Constructions.agda` already had.
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ'} {τ : SortedSig S ℓ2 ℓ'}
  (σeq : SortedEqns σ ℓ1'' ℓv) (τeq : SortedEqns τ ℓ2'' ℓv)
  (ℓX : Level) where

  pInlᶜ : PresEqnsᶜ σeq (σeq ⊕Eqns τeq) ℓX (inlSigMapᶠ σ τ)
  pInlᶜ X α sat = satl σeq τeq (Cay (λ s → ⟨ X s ⟩)) α sat

  pInrᶜ : PresEqnsᶜ τeq (σeq ⊕Eqns τeq) ℓX (inrSigMapᶠ σ τ)
  pInrᶜ X α sat = satr σeq τeq (Cay (λ s → ⟨ X s ⟩)) α sat

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ'} {τ : SortedSig S ℓ2 ℓ'}
  {υ : SortedSig S ℓ3 ℓ'}
  {σeq : SortedEqns σ ℓ1'' ℓv} {τeq : SortedEqns τ ℓ2'' ℓv}
  {υeq : SortedEqns υ ℓ3'' ℓv}
  {F : SortedSigMapᶠ σ υ} {G : SortedSigMapᶠ τ υ} {ℓX : Level}
  (pF : PresEqnsᶜ σeq υeq ℓX F) (pG : PresEqnsᶜ τeq υeq ℓX G) where

  -- `resl (resOpsᶜ [ F , G ] X α)` is `resOpsᶜ F X α`, again
  -- definitionally, since `[ F , G ]SigMapᶠ` is defined by a case split
  -- that `inl`/`inr` resolve.
  [_,_]Eqnsᶜ : PresEqnsᶜ (σeq ⊕Eqns τeq) υeq ℓX [ F , G ]SigMapᶠ
  [_,_]Eqnsᶜ X α sat (inl e) ρ =
      TmRec-inl σ τ Y β ρ (σeq .lhs e)
    ∙ pF X α sat e ρ
    ∙ sym (TmRec-inl σ τ Y β ρ (σeq .rhs e))
    where
      Y = Cay (λ s → ⟨ X s ⟩)
      β = resOpsᶜ [ F , G ]SigMapᶠ (λ s → ⟨ X s ⟩) α
  [_,_]Eqnsᶜ X α sat (inr e) ρ =
      TmRec-inr σ τ Y β ρ (τeq .lhs e)
    ∙ pG X α sat e ρ
    ∙ sym (TmRec-inr σ τ Y β ρ (τeq .rhs e))
    where
      Y = Cay (λ s → ⟨ X s ⟩)
      β = resOpsᶜ [ F , G ]SigMapᶠ (λ s → ⟨ X s ⟩) α

-- ------------------------------------------------------------------
-- `σ ⊕Eqns τ` is the coproduct in `SORTEDTHEORY`
-- ------------------------------------------------------------------

module _ {S : Type ℓS} (isSetS : isSet S) (ℓ'' ℓv ℓX : Level)
  {σ τ : SortedSetSig S ℓ ℓ'}
  (σeq : SortedEqns (σ .sig) ℓ'' ℓv)
  (τeq : SortedEqns (τ .sig) ℓ'' ℓv) where

  private
    module Th = Category (SORTEDTHEORY isSetS ℓ'' ℓv ℓX ℓ ℓ')

  ⊕Theory : Th.ob
  ⊕Theory = (_⊕SortedSetSig_ isSetS σ τ) , (σeq ⊕Eqns τeq)

  inlTheory : Th.Hom[ (σ , σeq) , ⊕Theory ]
  inlTheory = inlSigMapᶠ (σ .sig) (τ .sig) , pInlᶜ σeq τeq ℓX

  inrTheory : Th.Hom[ (τ , τeq) , ⊕Theory ]
  inrTheory = inrSigMapᶠ (σ .sig) (τ .sig) , pInrᶜ σeq τeq ℓX

  SORTEDTHEORYBinCoproduct
    : BinCoproduct (SORTEDTHEORY isSetS ℓ'' ℓv ℓX ℓ ℓ') (σ , σeq) (τ , τeq)
  SORTEDTHEORYBinCoproduct .BinCoproduct.binCoprodOb = ⊕Theory
  SORTEDTHEORYBinCoproduct .BinCoproduct.binCoprodInj₁ = inlTheory
  SORTEDTHEORYBinCoproduct .BinCoproduct.binCoprodInj₂ = inrTheory
  SORTEDTHEORYBinCoproduct .BinCoproduct.univProp
    {z = υ , υeq} (F , pF) (G , pG) .fst =
    ([ F , G ]SigMapᶠ , [ pF , pG ]Eqnsᶜ)
    , Σ≡Prop (λ f → isPropPresEqnsᶜ σeq υeq ℓX f isSetS) refl
    , Σ≡Prop (λ f → isPropPresEqnsᶜ τeq υeq ℓX f isSetS) refl
  SORTEDTHEORYBinCoproduct .BinCoproduct.univProp
    {z = υ , υeq} (F , pF) (G , pG) .snd ((H , pH) , p , q) =
    Σ≡Prop
      (λ _ → isProp×
        (Th.isSetHom {x = σ , σeq} {y = υ , υeq} _ _)
        (Th.isSetHom {x = τ , τeq} {y = υ , υeq} _ _))
      (Σ≡Prop
        (λ f → isPropPresEqnsᶜ (σeq ⊕Eqns τeq) υeq ℓX f isSetS)
        (cong₂ (λ F' G' → [ F' , G' ]SigMapᶠ)
          (sym (cong fst p)) (sym (cong fst q))
         ∙ ⊕SigMapᶠη H))

-- ------------------------------------------------------------------
-- The point of the construction: models on a shared carrier
-- ------------------------------------------------------------------
--
-- `ModOn σeq X` is the fibre of `MODᴰ σeq ℓX` over the carrier family
-- `X`: an interpretation of the operations together with a proof that
-- the equations hold.  It is what `Alg` is in the single-sorted layer.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  (X : S → hSet ℓX) where

  ModOn : Type _
  ModOn = Categoryᴰ.ob[_] (MODᴰ σeq ℓX) X

  isPropSat : (α : Ops {σ = σ} (λ s → ⟨ X s ⟩))
    → isProp ((e : σeq .eqns)
              (ρ : (v : σeq .vars e) → ⟨ X (σeq .varSort e v) ⟩)
            → TmRec (λ s → ⟨ X s ⟩) α ρ (σeq .lhs e)
              ≡ TmRec (λ s → ⟨ X s ⟩) α ρ (σeq .rhs e))
  isPropSat α = isPropΠ2 (λ e ρ → X (σeq .eqnSort e) .snd _ _)

  ModOn≡ : {M N : ModOn} → M .fst ≡ N .fst → M ≡ N
  ModOn≡ = Σ≡Prop isPropSat

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ'} {τ : SortedSig S ℓ2 ℓ'}
  (σeq : SortedEqns σ ℓ1'' ℓv) (τeq : SortedEqns τ ℓ2'' ℓv)
  (X : S → hSet ℓX) where

  private
    Y : S → Type ℓX
    Y s = ⟨ X s ⟩

  -- `resl Y (⊕Ops α β) ≡ α` and `resr Y (⊕Ops α β) ≡ β` are both `refl`
  ⊕Ops : Ops {σ = σ} Y → Ops {σ = τ} Y → Ops {σ = σ ⊕Sig τ} Y
  ⊕Ops α β (inl o) = α o
  ⊕Ops α β (inr o) = β o

  module _ (M : ModOn σeq X) (N : ModOn τeq X) where
    private
      α = M .fst
      β = N .fst
      γ = ⊕Ops α β

    ⊕Sat : (e : (σeq ⊕Eqns τeq) .eqns)
      (ρ : (v : (σeq ⊕Eqns τeq) .vars e)
         → Y ((σeq ⊕Eqns τeq) .varSort e v))
      → TmRec Y γ ρ ((σeq ⊕Eqns τeq) .lhs e)
        ≡ TmRec Y γ ρ ((σeq ⊕Eqns τeq) .rhs e)
    ⊕Sat (inl e) ρ =
        TmRec-inl σ τ Y γ ρ (σeq .lhs e)
      ∙ M .snd e ρ
      ∙ sym (TmRec-inl σ τ Y γ ρ (σeq .rhs e))
    ⊕Sat (inr e) ρ =
        TmRec-inr σ τ Y γ ρ (τeq .lhs e)
      ∙ N .snd e ρ
      ∙ sym (TmRec-inr σ τ Y γ ρ (τeq .rhs e))

    ⊕Mod : ModOn (σeq ⊕Eqns τeq) X
    ⊕Mod = γ , ⊕Sat

  ⊕ModIso : Iso (ModOn (σeq ⊕Eqns τeq) X) (ModOn σeq X × ModOn τeq X)
  ⊕ModIso .Iso.fun M =
      (resl σ τ Y (M .fst) , satl σeq τeq Y (M .fst) (M .snd))
    , (resr σ τ Y (M .fst) , satr σeq τeq Y (M .fst) (M .snd))
  ⊕ModIso .Iso.inv (M , N) = ⊕Mod M N
  ⊕ModIso .Iso.sec (M , N) =
    ΣPathP (ModOn≡ σeq X refl , ModOn≡ τeq X refl)
  ⊕ModIso .Iso.ret M =
    ModOn≡ (σeq ⊕Eqns τeq) X
      (funExt (λ { (inl o) → refl ; (inr o) → refl }))

  -- what the round trips actually are.  On the *operations* they are
  -- `refl`: `sec` on the nose, `ret` after the case split that `_⊎_`'s
  -- missing η forces.  Only the equation components move, and they are
  -- propositions, so `Σ≡Prop` is all that is needed.
  ⊕ModIso-secOpsL : (M : ModOn σeq X) (N : ModOn τeq X)
    → ⊕ModIso .Iso.fun (⊕ModIso .Iso.inv (M , N)) .fst .fst ≡ M .fst
  ⊕ModIso-secOpsL M N = refl

  ⊕ModIso-secOpsR : (M : ModOn σeq X) (N : ModOn τeq X)
    → ⊕ModIso .Iso.fun (⊕ModIso .Iso.inv (M , N)) .snd .fst ≡ N .fst
  ⊕ModIso-secOpsR M N = refl

  ⊕ModIso-retOpsL : (M : ModOn (σeq ⊕Eqns τeq) X) (o : σ .ops)
    → ⊕ModIso .Iso.inv (⊕ModIso .Iso.fun M) .fst (inl o) ≡ M .fst (inl o)
  ⊕ModIso-retOpsL M o = refl

  ⊕ModIso-retOpsR : (M : ModOn (σeq ⊕Eqns τeq) X) (o : τ .ops)
    → ⊕ModIso .Iso.inv (⊕ModIso .Iso.fun M) .fst (inr o) ≡ M .fst (inr o)
  ⊕ModIso-retOpsR M o = refl
