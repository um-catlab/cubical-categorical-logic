{-# OPTIONS --lossy-unification #-}
-- Weighted limits as strict presheaf homs: ⟦ W , D ⟧ is the W-weighted
-- limit of D, and Nerve is ⟦ K - , D ⟧ for a shape family K.
module Cubical.Categories.Limits.Weighted where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Yoneda using (yo)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.StrictHom.Base

private
  variable
    ℓc ℓc' ℓj ℓj' ℓw ℓw' ℓd ℓd' ℓv : Level

open Functor
open Iso
open NatTrans
open PshHomStrict

module _ {J : Category ℓj ℓj'} where

  ⟦_,_⟧ : (W : Presheaf J ℓw) (D : Presheaf J ℓd)
        → hSet (ℓ-max (ℓ-max ℓj ℓj') (ℓ-max ℓw ℓd))
  ⟦ W , D ⟧ = PshHomStrict W D , isSetPshHomStrict W D

  module _ {W : Presheaf J ℓw} {D : Presheaf J ℓd} where

    leg : ⟨ ⟦ W , D ⟧ ⟩ → (j : J .Category.ob) → ⟨ W .F-ob j ⟩ → ⟨ D .F-ob j ⟩
    leg α = α .N-ob

    legNat : (α : ⟨ ⟦ W , D ⟧ ⟩) → PshHomStrictN-homTy W D (leg α)
    legNat α = α .N-hom

    limPath : {α β : ⟨ ⟦ W , D ⟧ ⟩} → leg α ≡ leg β → α ≡ β
    limPath = makePshHomStrictPath

module _ {J : Category ℓj ℓj'} {D : Presheaf J ℓd} where

  reindW : {W' : Presheaf J ℓw'} {W : Presheaf J ℓw}
         → PshHomStrict W' W → ⟨ ⟦ W , D ⟧ ⟩ → ⟨ ⟦ W' , D ⟧ ⟩
  reindW u α = u ⋆PshHomStrict α

  reindW-id : {W : Presheaf J ℓw} (α : ⟨ ⟦ W , D ⟧ ⟩)
            → reindW idPshHomStrict α ≡ α
  reindW-id α = refl

  reindW-seq : {W'' : Presheaf J ℓw'} {W' W : Presheaf J ℓw}
               (u : PshHomStrict W'' W') (v : PshHomStrict W' W)
               (α : ⟨ ⟦ W , D ⟧ ⟩)
             → reindW (u ⋆PshHomStrict v) α ≡ reindW u (reindW v α)
  reindW-seq u v α = refl

module _ {J : Category ℓj ℓj'} {W : Presheaf J ℓw} where

  mapD : {D : Presheaf J ℓd} {D' : Presheaf J ℓd'}
       → PshHomStrict D D' → ⟨ ⟦ W , D ⟧ ⟩ → ⟨ ⟦ W , D' ⟧ ⟩
  mapD φ α = α ⋆PshHomStrict φ

  mapD-id : {D : Presheaf J ℓd} (α : ⟨ ⟦ W , D ⟧ ⟩)
          → mapD idPshHomStrict α ≡ α
  mapD-id α = refl

  mapD-seq : {D : Presheaf J ℓd} {D' D'' : Presheaf J ℓd'}
             (φ : PshHomStrict D D') (ψ : PshHomStrict D' D'')
             (α : ⟨ ⟦ W , D ⟧ ⟩)
           → mapD (φ ⋆PshHomStrict ψ) α ≡ mapD ψ (mapD φ α)
  mapD-seq φ ψ α = refl

module _ {J : Category ℓj ℓj'} (D : Presheaf J ℓd) where
  private module J = Category J

  evalW : (j : J.ob) → Iso ⟨ ⟦ yo j , D ⟧ ⟩ ⟨ D .F-ob j ⟩
  evalW j .fun α = α .N-ob j J.id
  evalW j .inv d = pshhom
    (λ y f → D .F-hom f d)
    (λ c c' f p' p e →
      sym (funExt⁻ (D .F-seq p' f) d) ∙ cong (λ k → D .F-hom k d) e)
  evalW j .sec d = funExt⁻ (D .F-id) d
  evalW j .ret α = limPath (funExt λ y → funExt λ f →
    α .N-hom y j f J.id f (J.⋆IdR f))

module _ {J : Category ℓj ℓj'} (D : Presheaf J ℓd) where
  private module J = Category J

  ConicalLim : hSet _
  ConicalLim = ⟦ UnitPsh {C = J} , D ⟧

  ConeΣ : Type (ℓ-max (ℓ-max ℓj ℓj') ℓd)
  ConeΣ = Σ[ t ∈ ((j : J.ob) → ⟨ D .F-ob j ⟩) ]
           ((c c' : J.ob) (f : J [ c , c' ]) → D .F-hom f (t c') ≡ t c)

  isPropConeNat : (t : (j : J.ob) → ⟨ D .F-ob j ⟩)
    → isProp ((c c' : J.ob) (f : J [ c , c' ]) → D .F-hom f (t c') ≡ t c)
  isPropConeNat t = isPropΠ3 λ c _ _ → D .F-ob c .snd _ _

  conicalIso : Iso ⟨ ConicalLim ⟩ ConeΣ
  conicalIso .fun α = (λ j → α .N-ob j tt)
                    , (λ c c' f → α .N-hom c c' f tt tt refl)
  conicalIso .inv (t , nat) = pshhom (λ j _ → t j) (λ c c' f _ _ _ → nat c c' f)
  conicalIso .sec (t , nat) = Σ≡Prop isPropConeNat refl
  conicalIso .ret α = limPath refl

module _ {J : Category ℓj ℓj'} where

  _^_ : (D : Presheaf J ℓd) (V : hSet ℓv) → Presheaf J (ℓ-max ℓd ℓv)
  (D ^ V) .F-ob j = (⟨ V ⟩ → ⟨ D .F-ob j ⟩) , isSetΠ (λ _ → D .F-ob j .snd)
  (D ^ V) .F-hom f t = λ v → D .F-hom f (t v)
  (D ^ V) .F-id = funExt λ t → funExt λ v → funExt⁻ (D .F-id) (t v)
  (D ^ V) .F-seq f g = funExt λ t → funExt λ v → funExt⁻ (D .F-seq f g) (t v)

  curryW : {W : Presheaf J ℓw} {D : Presheaf J ℓd} {V : hSet ℓv}
         → Iso (⟨ V ⟩ → ⟨ ⟦ W , D ⟧ ⟩) ⟨ ⟦ W , D ^ V ⟧ ⟩
  curryW .fun g = pshhom
    (λ j w v → g v .N-ob j w)
    (λ c c' f p' p e → funExt λ v → g v .N-hom c c' f p' p e)
  curryW .inv α v = pshhom
    (λ j w → α .N-ob j w v)
    (λ c c' f p' p e → funExt⁻ (α .N-hom c c' f p' p e) v)
  curryW .sec α = limPath refl
  curryW .ret g = funExt λ v → limPath refl

module _ {C : Category ℓc ℓc'} {J : Category ℓj ℓj'} where

  Nerve : Functor C (PRESHEAF J ℓw) → Presheaf J ℓd
        → Presheaf C (ℓ-max (ℓ-max ℓj ℓj') (ℓ-max ℓw ℓd))
  Nerve K D .F-ob c     = ⟦ K .F-ob c , D ⟧
  Nerve K D .F-hom f α  = K .F-hom f ⋆PshHomStrict α
  Nerve K D .F-id       = funExt λ α → cong (_⋆PshHomStrict α) (K .F-id)
  Nerve K D .F-seq f g  = funExt λ α → cong (_⋆PshHomStrict α) (K .F-seq g f)

  NerveMap : {K' K : Functor C (PRESHEAF J ℓw)} (u : NatTrans K' K)
             (D : Presheaf J ℓd)
           → PshHomStrict (Nerve K D) (Nerve K' D)
  NerveMap u D .N-ob c α = u .N-ob c ⋆PshHomStrict α
  NerveMap {K' = K'} u D .N-hom c c' f α' α e =
    cong (_⋆PshHomStrict α') (u .N-hom f)
    ∙ cong (u .N-ob c ⋆PshHomStrict_) e
