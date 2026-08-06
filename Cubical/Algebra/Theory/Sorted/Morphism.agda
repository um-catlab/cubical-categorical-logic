{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.Theory.Sorted.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base

open import Cubical.Algebra.Theory.Sorted
open import Cubical.Algebra.Theory.Sorted.Constructions

private
  variable
    ℓS ℓ1 ℓ1' ℓ2 ℓ2' ℓ3 ℓ3' : Level
    ℓ1'' ℓ2'' ℓv ℓw ℓX : Level

open SortedSig
open SortedEqns
open Functor

record SortedSigMap {S : Type ℓS}
  (σ : SortedSig S ℓ1 ℓ1') (τ : SortedSig S ℓ2 ℓ2')
  : Type (ℓ-max ℓS (ℓ-max ℓ1 (ℓ-max ℓ2 (ℓ-max ℓ1' ℓ2')))) where
  field
    onOps : σ .ops → τ .ops
    unArity : (o : σ .ops) → τ .arities (onOps o) → σ .arities o
    onSortOf : (o : σ .ops) (a : τ .arities (onOps o))
      → σ .sortOf o (unArity o a) Eq.≡ τ .sortOf (onOps o) a
    onResult : (o : σ .ops) → σ .resultSort o Eq.≡ τ .resultSort (onOps o)

open SortedSigMap

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} where

  idSortedSigMap : SortedSigMap σ σ
  idSortedSigMap .onOps o = o
  idSortedSigMap .unArity o a = a
  idSortedSigMap .onSortOf o a = Eq.refl
  idSortedSigMap .onResult o = Eq.refl

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {υ : SortedSig S ℓ3 ℓ3'} (F : SortedSigMap σ τ) (G : SortedSigMap τ υ)
  where

  _⋆SigMap_ : SortedSigMap σ υ
  _⋆SigMap_ .onOps o = G .onOps (F .onOps o)
  _⋆SigMap_ .unArity o a = F .unArity o (G .unArity (F .onOps o) a)
  _⋆SigMap_ .onSortOf o a =
    F .onSortOf o (G .unArity (F .onOps o) a)
    Eq.∙ G .onSortOf (F .onOps o) a
  _⋆SigMap_ .onResult o =
    F .onResult o Eq.∙ G .onResult (F .onOps o)

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (F : SortedSigMap σ τ) where

  ⋆SigMapIdL : (idSortedSigMap ⋆SigMap F) ≡ F
  ⋆SigMapIdL = refl

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (F : SortedSigMap σ τ) where

  resOps : (X : S → Type ℓX) → Ops {σ = τ} X → Ops {σ = σ} X
  resOps X α o x =
    Eq.transport X (Eq.sym (F .onResult o))
      (α (F .onOps o)
        (λ a → Eq.transport X (F .onSortOf o a) (x (F .unArity o a))))

  mapTm : {V : Type ℓv} {vs : V → S} {s : S}
    → Tm σ V vs s → Tm τ V vs s
  mapTm (var v) = var v
  mapTm {V = V} {vs = vs} (node o ts) =
    Eq.transport (Tm τ V vs) (Eq.sym (F .onResult o))
      (node (F .onOps o)
        (λ a → Eq.transport (Tm τ V vs) (F .onSortOf o a)
                 (mapTm (ts (F .unArity o a)))))

  module _ (X : S → Type ℓX) (α : Ops {σ = τ} X)
    {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v)) where

    private
      TmRec-Eq : {s s' : S} (p : s Eq.≡ s') (t : Tm τ V vs s)
        → TmRec X α ρ (Eq.transport (Tm τ V vs) p t)
          ≡ Eq.transport X p (TmRec X α ρ t)
      TmRec-Eq Eq.refl t = refl

    TmRec-mapTm : {s : S} (M : Tm σ V vs s)
      → TmRec X (resOps X α) ρ M ≡ TmRec X α ρ (mapTm M)
    TmRec-mapTm (var v) = refl
    TmRec-mapTm (node o ts) =
      cong (Eq.transport X (Eq.sym (F .onResult o)))
        (cong (α (F .onOps o))
          (funExt (λ a →
            cong (Eq.transport X (F .onSortOf o a))
              (TmRec-mapTm (ts (F .unArity o a)))
            ∙ sym (TmRec-Eq (F .onSortOf o a)
                    (mapTm (ts (F .unArity o a)))))))
      ∙ sym (TmRec-Eq (Eq.sym (F .onResult o)) _)

  private
    natEq : {X Y : S → Type ℓX} (f : (s : S) → X s → Y s)
      {s s' : S} (p : s Eq.≡ s') (z : X s)
      → f s' (Eq.transport X p z) ≡ Eq.transport Y p (f s z)
    natEq f Eq.refl z = refl

  resHomCond : {X Y : S → Type ℓX}
    (f : (s : S) → X s → Y s)
    (α : Ops {σ = τ} X) (β : Ops {σ = τ} Y)
    → ((o : τ .ops) (x : (a : τ .arities o) → X (τ .sortOf o a))
       (y : X (τ .resultSort o)) → y ≡ α o x
       → f (τ .resultSort o) y ≡ β o (λ a → f (τ .sortOf o a) (x a)))
    → (o : σ .ops) (x : (a : σ .arities o) → X (σ .sortOf o a))
      (y : X (σ .resultSort o)) → y ≡ resOps X α o x
    → f (σ .resultSort o) y ≡ resOps Y β o (λ a → f (σ .sortOf o a) (x a))
  resHomCond {X = X} {Y = Y} f α β ϕ o x y eq =
    cong (f (σ .resultSort o)) eq
    ∙ natEq f (Eq.sym (F .onResult o)) _
    ∙ cong (Eq.transport Y (Eq.sym (F .onResult o)))
        (ϕ (F .onOps o) _ _ refl
         ∙ cong (β (F .onOps o))
             (funExt (λ a → natEq f (F .onSortOf o a) (x (F .unArity o a)))))

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (σeq : SortedEqns σ ℓ1'' ℓv) (τeq : SortedEqns τ ℓ2'' ℓw)
  (ℓX : Level) (F : SortedSigMap σ τ) where

  PresEqns : Type _
  PresEqns = (M : Category.ob (MOD τeq ℓX))
    (e : σeq .eqns) (ρ : (v : σeq .vars e) → ⟨ M .fst (σeq .varSort e v) ⟩)
    → TmRec (λ s → ⟨ M .fst s ⟩)
        (resOps F (λ s → ⟨ M .fst s ⟩) (M .snd .fst)) ρ (σeq .lhs e)
      ≡ TmRec (λ s → ⟨ M .fst s ⟩)
          (resOps F (λ s → ⟨ M .fst s ⟩) (M .snd .fst)) ρ (σeq .rhs e)

  isPropPresEqns : isProp PresEqns
  isPropPresEqns =
    isPropΠ3 (λ M e _ → M .fst (σeq .eqnSort e) .snd _ _)

  module _ (pres : PresEqns) where

    resModOb : Category.ob (MOD τeq ℓX) → Category.ob (MOD σeq ℓX)
    resModOb M =
      M .fst
      , resOps F (λ s → ⟨ M .fst s ⟩) (M .snd .fst)
      , pres M

    resModHom : (M N : Category.ob (MOD τeq ℓX))
      → ModHom τeq ℓX M N → ModHom σeq ℓX (resModOb M) (resModOb N)
    resModHom M N (f , ϕ , _) =
      f
      , resHomCond F f (M .snd .fst) (N .snd .fst) ϕ
      , tt*

    private
      module Mσ = Categoryᴰ (MODᴰ σeq ℓX)

      isPropHomᴰ : {X Y : Category.ob (FAM S ℓX)}
        (f : Category.Hom[_,_] (FAM S ℓX) X Y)
        (Mᴰ : Mσ.ob[ X ]) (Nᴰ : Mσ.ob[ Y ])
        → isProp (Mσ.Hom[ f ][ Mᴰ , Nᴰ ])
      isPropHomᴰ {Y = Y} f Mᴰ Nᴰ =
        isPropΣ (isPropΠ4 (λ _ _ _ _ → Y _ .snd _ _))
                (λ _ → isPropUnit*)

    resMod : Functor (MOD τeq ℓX) (MOD σeq ℓX)
    resMod .F-ob = resModOb
    resMod .F-hom {x = M} {y = N} = resModHom M N
    resMod .F-id {x = M} =
      Σ≡Prop (λ f → isPropHomᴰ f _ _) refl
    resMod .F-seq {x = M} {y = N} {z = P} h k =
      Σ≡Prop (λ f → isPropHomᴰ f _ _) refl

module _ {S : Type ℓS} (σ : SortedSig S ℓ1 ℓ1') (τ : SortedSig S ℓ2 ℓ1')
  where

  inlSigMap : SortedSigMap σ (σ ⊕Sig τ)
  inlSigMap .onOps = inl
  inlSigMap .unArity o a = a
  inlSigMap .onSortOf o a = Eq.refl
  inlSigMap .onResult o = Eq.refl

  inrSigMap : SortedSigMap τ (σ ⊕Sig τ)
  inrSigMap .onOps = inr
  inrSigMap .unArity o a = a
  inrSigMap .onSortOf o a = Eq.refl
  inrSigMap .onResult o = Eq.refl

  resOps-inl : (X : S → Type ℓX) (α : Ops {σ = σ ⊕Sig τ} X)
    → resOps inlSigMap X α ≡ resl σ τ X α
  resOps-inl X α = refl

  resOps-inr : (X : S → Type ℓX) (α : Ops {σ = σ ⊕Sig τ} X)
    → resOps inrSigMap X α ≡ resr σ τ X α
  resOps-inr X α = refl

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ1'}
  (σeq : SortedEqns σ ℓ1'' ℓv) (E : SortedEqns (σ ⊕Sig τ) ℓ2'' ℓv)
  (ℓX : Level) where

  presEqnsInl :
    PresEqns σeq (injEqnsL τ σeq ∪Eqns E) ℓX (inlSigMap σ τ)
  presEqnsInl M e ρ =
    sym (TmRec-inl σ τ X (M .snd .fst) ρ (σeq .lhs e))
    ∙ M .snd .snd (inl e) ρ
    ∙ TmRec-inl σ τ X (M .snd .fst) ρ (σeq .rhs e)
    where
      X : S → Type ℓX
      X s = ⟨ M .fst s ⟩

  -- and hence a model of the extension restricts to a model of σeq
  resModInl : Category.ob (MOD (injEqnsL τ σeq ∪Eqns E) ℓX)
    → Category.ob (MOD σeq ℓX)
  resModInl =
    resModOb σeq (injEqnsL τ σeq ∪Eqns E) ℓX (inlSigMap σ τ) presEqnsInl
