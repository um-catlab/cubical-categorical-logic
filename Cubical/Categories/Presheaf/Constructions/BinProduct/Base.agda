{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.BinProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Unit
open import Cubical.HITs.PathEq
open import Cubical.HITs.Join

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Profunctor.Constructions.Extension
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Yoneda.More

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓR ℓS : Level

open Functor
open PshHom
open PshIso

module _ {C : Category ℓ ℓ'} where
  private
    module C = Category C
  PshProd' : Functor
    (PresheafCategory C ℓA ×C PresheafCategory C ℓB)
    (PresheafCategory C (ℓ-max ℓA ℓB))
  PshProd' = (postcomposeF _ ×Sets ∘F ,F-functor)

  PshProd : Bifunctor (PresheafCategory C ℓA) (PresheafCategory C ℓB)
                      (PresheafCategory C (ℓ-max ℓA ℓB))
  PshProd = ParFunctorToBifunctor PshProd'

  -×Psh_ : Presheaf C ℓA → Functor (PresheafCategory C ℓB) (PresheafCategory C (ℓ-max ℓA ℓB))
  -×Psh Q = appR PshProd Q

  _×Psh- : Presheaf C ℓA → Functor (PresheafCategory C ℓB) (PresheafCategory C (ℓ-max ℓA ℓB))
  P ×Psh- = appL PshProd P

  _×Psh_ : Presheaf C ℓA → Presheaf C ℓB → Presheaf C _
  P ×Psh Q = PshProd ⟅ P , Q ⟆b

  -- irritatingly not definitional...
  -×Psh-Fob : ∀ (P : Presheaf C ℓP) (Q : Presheaf C ℓQ)
    → PshIso (P ×Psh Q) ((-×Psh Q) ⟅ P ⟆)
  -×Psh-Fob P Q = eqToPshIso (F-ob (-×Psh Q) P) Eq.refl Eq.refl

  private
    testPshProd : ∀ (P : Presheaf C ℓA)(Q : Presheaf C ℓB)
      → P ×Psh Q ≡ ×Sets ∘F (P ,F Q)
    testPshProd P Q = refl

  module _ (P : Presheaf C ℓA)(Q : Presheaf C ℓB) where
    π₁Strict : PshHom' (P ×Psh Q) P
    π₁Strict .PshHom'.N-ob _ = fst
    π₁Strict .PshHom'.N-hom _ _ _ _ = inr Eq.refl

    π₂Strict : PshHom' (P ×Psh Q) Q
    π₂Strict .PshHom'.N-ob _ = snd
    π₂Strict .PshHom'.N-hom _ _ _ _ = inr Eq.refl

    π₁ : PshHom (P ×Psh Q) P
    π₁ .N-ob _ = fst
    π₁ .N-hom _ _ _ _ = refl

    π₂ : PshHom (P ×Psh Q) Q
    π₂ .N-ob _ = snd
    π₂ .N-hom _ _ _ _ = refl

    π₁Eq : PshHomEq (P ×Psh Q) P
    π₁Eq .PshHomEq.N-ob _ = fst
    π₁Eq .PshHomEq.N-hom _ _ _ _ _ Eq.refl = Eq.refl

    π₂Eq : PshHomEq (P ×Psh Q) Q
    π₂Eq .PshHomEq.N-ob _ = snd
    π₂Eq .PshHomEq.N-hom _ _ _ _ _ Eq.refl = Eq.refl

  module _
    {P : Presheaf C ℓA}
    {Q : Presheaf C ℓB}
    {R : Presheaf C ℓA'}
    (α : PshHom R P)
    (β : PshHom R Q)
    where
    ×PshIntro : PshHom R (P ×Psh Q)
    ×PshIntro .N-ob c x = (α .N-ob c x) , (β .N-ob c x)
    ×PshIntro .N-hom c c' f p =
      cong₂ _,_ (α .N-hom c c' f p) (β .N-hom c c' f p)

    ×Pshβ₁ : ×PshIntro ⋆PshHom π₁ P Q ≡ α
    ×Pshβ₁ = makePshHomPath refl

    ×Pshβ₂ : ×PshIntro ⋆PshHom π₂ P Q ≡ β
    ×Pshβ₂ = makePshHomPath refl

  module _
    {P : Presheaf C ℓA}
    {Q : Presheaf C ℓB}
    {R : Presheaf C ℓA'}
    (α : PshHomEq R P)
    (β : PshHomEq R Q)
    where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
    ×PshIntroEq : PshHomEq R (P ×Psh Q)
    ×PshIntroEq .PshHomEq.N-ob = λ c z → α .PshHomEq.N-ob c z , β .PshHomEq.N-ob c z
    ×PshIntroEq .PshHomEq.N-hom _ _ f r' r f⋆r'≡r =
      Eq.≡-× (α .PshHomEq.N-hom _ _ f r' r f⋆r'≡r) (β .PshHomEq.N-hom _ _ f r' r f⋆r'≡r)

    ×Pshβ₁Eq : ×PshIntroEq ⋆PshHomEq π₁Eq P Q ≡ α
    ×Pshβ₁Eq = makePshHomEqPath refl

  ΔPshHom : {P : Presheaf C ℓA} → PshHom P (P ×Psh P)
  ΔPshHom = ×PshIntro idPshHom idPshHom

  module _ (P : Presheaf C ℓA)(Q : Presheaf C ℓB) where
    ×Psh-UMP : ∀ {R : Presheaf C ℓA'} → Iso (PshHom R (P ×Psh Q)) (PshHom R P × PshHom R Q)
    ×Psh-UMP .Iso.fun α = (α ⋆PshHom π₁ P Q) , (α ⋆PshHom π₂ P Q)
    ×Psh-UMP .Iso.inv (α , β) = ×PshIntro α β
    ×Psh-UMP .Iso.sec (α , β) = ΣPathP ((×Pshβ₁ α β) , (×Pshβ₂ α β))
    ×Psh-UMP .Iso.ret α = makePshHomPath refl

  module _
    {P : Presheaf C ℓA}
    {P' : Presheaf C ℓA'}
    {Q : Presheaf C ℓB}
    {Q' : Presheaf C ℓB'}
    where
    _×PshHom_ : PshHom P P' → PshHom Q Q' → PshHom (P ×Psh Q) (P' ×Psh Q')
    α ×PshHom β = ×PshIntro (π₁ P Q ⋆PshHom α) (π₂ P Q ⋆PshHom β)
    _×PshHomEq_ : PshHomEq P P' → PshHomEq Q Q' → PshHomEq (P ×Psh Q) (P' ×Psh Q')
    α ×PshHomEq β = ×PshIntroEq (π₁Eq P Q ⋆PshHomEq α) (π₂Eq P Q ⋆PshHomEq β)
  module _
    {P : Presheaf C ℓA}
    {P' : Presheaf C ℓA'}
    {Q : Presheaf C ℓB}
    {Q' : Presheaf C ℓB'}
    (PIso : PshIso P P')
    (QIso : PshIso Q Q')
    where
    ×PshIso : PshIso (P ×Psh Q) (P' ×Psh Q')
    ×PshIso .trans = (PIso .trans ×PshHom QIso .trans)
    ×PshIso .nIso c .fst x =
      PIso .nIso c .fst (x .fst) ,
      QIso .nIso c .fst (x .snd)
    ×PshIso .nIso c .snd .fst b =
      cong₂ _,_
        (PIso .nIso c .snd .fst (b .fst))
        (QIso .nIso c .snd .fst (b .snd))
    ×PshIso .nIso c .snd .snd b =
      cong₂ _,_
        (PIso .nIso c .snd .snd (b .fst))
        (QIso .nIso c .snd .snd (b .snd))

  module _
    {P : Presheaf C ℓA}
    {P' : Presheaf C ℓA'}
    {Q : Presheaf C ℓB}
    {Q' : Presheaf C ℓB'}
    (PIso : PshIsoEq P P')
    (QIso : PshIsoEq Q Q')
    where
    ×PshIsoEq : PshIsoEq (P ×Psh Q) (P' ×Psh Q')
    ×PshIsoEq .PshIsoEq.isos c = ×-cong-Iso (PIso .PshIsoEq.isos c) (QIso .PshIsoEq.isos c)
    ×PshIsoEq .PshIsoEq.nat =
      (PshIsoEq.toPshHomEq PIso ×PshHomEq PshIsoEq.toPshHomEq QIso) .PshHomEq.N-hom
  private
    open Category
    open Bifunctor
    open NatTrans
    -- Test to make sure we get the right definitional
    -- behavior for Bif-homL, Bif-homR
    module _ (P P' : Presheaf C ℓA)(Q Q' : Presheaf C ℓB)
             (α : PresheafCategory C ℓA [ P , P' ])
             (β : PresheafCategory C ℓB [ Q , Q' ])
             c where

      _ : PshProd .Bif-homL α Q .N-ob c ≡ λ (p , q) → α .N-ob c p , q
      _ = refl

      _ : PshProd .Bif-homR P β .N-ob c ≡ λ (p , q) → p , β .N-ob c q
      _ = refl

module _ {C : Category ℓ ℓ'}{D : Category ℓD ℓD'}
  (F : Functor D C)
  (P : Presheaf C ℓA)(Q : Presheaf C ℓB) where
  reindPsh× : PshIso (reindPsh F (P ×Psh Q)) (reindPsh F P ×Psh reindPsh F Q)
  reindPsh× .trans = ×PshIntro (reindPshHom F (π₁ P Q)) (reindPshHom F (π₂ P Q))
  reindPsh× .nIso x .fst = λ z → z
  reindPsh× .nIso x .snd .fst b = refl
  reindPsh× .nIso x .snd .snd a = refl

module _ {C : Category ℓ ℓ'}{D : Category ℓD ℓD'} where

  module _
    (R : Bifunctor (D ^op) C (SET ℓR))
    (P : Presheaf D ℓP)
    (Q : Presheaf C ℓQ) where

    private
      module extRQ = PresheafNotation (ext R ⟅ Q ⟆)
      module extRQ×P = PresheafNotation ((ext R ⟅ Q ⟆) ×Psh P)
      module R⊗Q = ext-⊗ R Q
      module R×P⊗Q = ext-⊗ (CurriedToBifunctorL ((-×Psh P) ∘F CurryBifunctorL R)) Q
      module extR×PQ = PresheafNotation (ext (CurriedToBifunctorL ((-×Psh P) ∘F CurryBifunctorL R)) ⟅ Q ⟆)
      module P = PresheafNotation P

    -- (R(d,c) ⊗[ c ] Q(c,*)) × P(d,*) ≅ (R(d,c) × P(d,*)) ⊗[ c ] Q(c,*)
    ⊗×-comm :
      PshIso
        ((ext R ⟅ Q ⟆) ×Psh P)
        (ext (CurriedToBifunctorL ((-×Psh P) ∘F CurryBifunctorL R)) ⟅ Q ⟆)
    ⊗×-comm .trans .N-ob d =
      uncurry
        (R⊗Q.rec (isSet→ extR×PQ.isSetPsh)
          (λ r q p → (r , p) R×P⊗Q.,⊗ q)
          (λ r f q → funExt λ p → R×P⊗Q.swap (r , p) f q))
    ⊗×-comm .trans .N-hom c c' f =
      uncurry
        (R⊗Q.ind (λ _ → isPropΠ (λ _ → extR×PQ.isSetPsh _ _))
                 (λ r q p → refl))
    ⊗×-comm .nIso d =
      (R×P⊗Q.rec extRQ×P.isSetPsh (λ (r , p) q → (r R⊗Q.,⊗ q) , p) λ (r , p) f q → ΣPathP ((R⊗Q.swap r f q) , refl))
      , R×P⊗Q.ind (λ _ → extR×PQ.isSetPsh _ _) (λ _ _ → refl)
      , uncurry (R⊗Q.ind (λ _ → isPropΠ (λ _ → extRQ×P.isSetPsh _ _)) λ _ _ _ → refl)

module _ {C : Category ℓ ℓ'} where
  private
    module C = Category C

  -×Psh_-cocontinuous : (P : Presheaf C ℓA) → CoContinuous (-×Psh P)
  -×Psh P -cocontinuous Q =
    invPshIso (-×Psh-Fob Q P) -- just expanding definitions
  -- Q(c,*) × P(c,*)
    ⋆PshIso ((×PshIso (CoYoneda Q) idPshIso)
  -- (C(c,c') ⊗[ c' ] Q(c',*)) × P(c,*)
    ⋆PshIso (⊗×-comm (HomBif C) P Q))
  -- (C(c,c') × P(c,*)) ⊗[ c' ] Q(c',*)
