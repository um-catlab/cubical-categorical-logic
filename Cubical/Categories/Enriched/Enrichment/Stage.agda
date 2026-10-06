{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.Base

module Cubical.Categories.Enriched.Enrichment.Stage
  {ℓ ℓ' ℓS : Level} {A : Category ℓ ℓ'}
  {ℓC ℓC' : Level} {C : Category ℓC ℓC'} (ℰ : Enrichment C (PshMon.𝓟Mon A ℓS)) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Presheaf.StrictHom.Base

open Functor
open PshHomStrict
open PshMon A ℓS using (ℓm ; 𝟙)

private
  module A = Category A
  module C = Category C
  module ℰ = Enrichment ℰ

Stage : A.ob → Category ℓC ℓm
Stage c .Category.ob = C.ob
Stage c .Category.Hom[_,_] X Y = ⟨ ℰ.VE[ X , Y ] .F-ob c ⟩
Stage c .Category.id = ℰ.id .N-ob c tt*
Stage c .Category._⋆_ α β = ℰ.seq _ _ _ .N-ob c (α , β)
Stage c .Category.⋆IdL {X} {Y} α =
  sym (funExt⁻ (funExt⁻ (cong N-ob (ℰ.⋆IdL X Y)) c) (tt* , α))
Stage c .Category.⋆IdR {X} {Y} α =
  sym (funExt⁻ (funExt⁻ (cong N-ob (ℰ.⋆IdR X Y)) c) (α , tt*))
Stage c .Category.⋆Assoc {W} {X} {Y} {Z} α β γ =
  funExt⁻ (funExt⁻ (cong N-ob (ℰ.⋆Assoc W X Y Z)) c) (α , (β , γ))
Stage c .Category.isSetHom {X} {Y} = ℰ.VE[ X , Y ] .F-ob c .snd

module _ {c : A.ob} where
  infixr 9 _⋆ₛ_
  _⋆ₛ_ : ∀ {X Y Z} → Stage c [ X , Y ] → Stage c [ Y , Z ] → Stage c [ X , Z ]
  _⋆ₛ_ = Stage c .Category._⋆_

  idₛ : ∀ {X} → Stage c [ X , X ]
  idₛ = Stage c .Category.id

res : {c c' : A.ob} → A [ c' , c ] → Functor (Stage c) (Stage c')
res k .F-ob X = X
res k .F-hom {X} {Y} = ℰ.VE[ X , Y ] .F-hom k
res {c} {c'} k .F-id = ℰ.id .N-hom c' c k tt* tt* refl
res {c} {c'} k .F-seq α β = ℰ.seq _ _ _ .N-hom c' c k (α , β) _ refl

res-id : {c : A.ob} {X Y : C.ob} (α : Stage c [ X , Y ]) → res A.id ⟪ α ⟫ ≡ α
res-id {X = X} {Y} α = funExt⁻ (ℰ.VE[ X , Y ] .F-id) α

res-seq : {c c' c'' : A.ob} {X Y : C.ob} (k : A [ c' , c ]) (k' : A [ c'' , c' ])
  (α : Stage c [ X , Y ]) → res k' ⟪ res k ⟪ α ⟫ ⟫ ≡ res (k' A.⋆ k) ⟪ α ⟫
res-seq {X = X} {Y} k k' α = sym (funExt⁻ (ℰ.VE[ X , Y ] .F-seq k k') α)

at : (c : A.ob) → Functor C (Stage c)
at c .F-ob X = X
at c .F-hom f = ℰ.⌜ f ⌝ .N-ob c tt*
at c .F-id = funExt⁻ (funExt⁻ (cong N-ob ℰ.⌜id⌝) c) tt*
at c .F-seq f g = funExt⁻ (funExt⁻ (cong N-ob (ℰ.⌜⋆⌝ f g)) c) tt*

at-res : {X Y : C.ob} (f : C [ X , Y ]) {c c' : A.ob} (k : A [ c' , c ])
  → res k ⟪ at c ⟪ f ⟫ ⟫ ≡ at c' ⟪ f ⟫
at-res f k = ℰ.⌜ f ⌝ .N-hom _ _ k tt* tt* refl

module _ {X Y : C.ob} (s : ∀ c → Stage c [ X , Y ])
  (s-res : ∀ {c c'} (k : A [ c' , c ]) → res k ⟪ s c ⟫ ≡ s c') where
  private
    s̃ : PshHomStrict 𝟙 ℰ.VE[ X , Y ]
    s̃ .N-ob c _ = s c
    s̃ .N-hom c c' k _ _ _ = s-res k

  glue : C [ X , Y ]
  glue = ℰ.⌞ s̃ ⌟

  at-glue : ∀ c → at c ⟪ glue ⟫ ≡ s c
  at-glue c = cong (λ m → m .N-ob c tt*) (ℰ.⇄-agree← s̃)

stages-separate : {X Y : C.ob} {f g : C [ X , Y ]}
  → (∀ c → at c ⟪ f ⟫ ≡ at c ⟪ g ⟫) → f ≡ g
stages-separate {f = f} {g} p =
  sym (ℰ.⇄-agree→ f)
  ∙ cong ℰ.⌞_⌟ (makePshHomStrictPath (funExt λ c → funExt λ _ → p c))
  ∙ ℰ.⇄-agree→ g

module _ {X Y : C.ob} (e : ∀ c → CatIso (Stage c) X Y)
  (e-res : ∀ {c c'} (k : A [ c' , c ]) → res k ⟪ e c .fst ⟫ ≡ e c' .fst)
  (e⁻-res : ∀ {c c'} (k : A [ c' , c ]) → res k ⟪ e c .snd .isIso.inv ⟫ ≡ e c' .snd .isIso.inv) where
  glueIso : CatIso C X Y
  glueIso .fst = glue (λ c → e c .fst) e-res
  glueIso .snd .isIso.inv = glue (λ c → e c .snd .isIso.inv) e⁻-res
  glueIso .snd .isIso.sec = stages-separate λ c →
    at c .F-seq _ _ ∙ cong₂ _⋆ₛ_ (at-glue _ _ c) (at-glue _ _ c) ∙ e c .snd .isIso.sec ∙ sym (at c .F-id)
  glueIso .snd .isIso.ret = stages-separate λ c →
    at c .F-seq _ _ ∙ cong₂ _⋆ₛ_ (at-glue _ _ c) (at-glue _ _ c) ∙ e c .snd .isIso.ret ∙ sym (at c .F-id)

  at-glueIso : ∀ c → at c ⟪ glueIso .fst ⟫ ≡ e c .fst
  at-glueIso = at-glue _ _
