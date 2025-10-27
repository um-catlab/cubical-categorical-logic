{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Bifunctor

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓS : Level

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

  _×Psh_ : Presheaf C ℓA → Presheaf C ℓB → Presheaf C _
  P ×Psh Q = PshProd ⟅ P , Q ⟆b

  module _ (P : Presheaf C ℓA)(Q : Presheaf C ℓB) where
    π₁ : PshHom (P ×Psh Q) P
    π₁ .N-ob _ = fst
    π₁ .N-hom _ _ _ _ = refl

    π₂ : PshHom (P ×Psh Q) Q
    π₂ .N-ob _ = snd
    π₂ .N-hom _ _ _ _ = refl

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

  module _ (P : Presheaf C ℓA)(Q : Presheaf C ℓB) where
    ×PshUMP : ∀ {R : Presheaf C ℓA'} → Iso (PshHom R (P ×Psh Q)) (PshHom R P × PshHom R Q)
    ×PshUMP .Iso.fun α = (α ⋆PshHom π₁ P Q) , (α ⋆PshHom π₂ P Q)
    ×PshUMP .Iso.inv (α , β) = ×PshIntro α β
    ×PshUMP .Iso.rightInv (α , β) = ΣPathP ((×Pshβ₁ α β) , (×Pshβ₂ α β))
    ×PshUMP .Iso.leftInv α = makePshHomPath refl

  module _
    {P : Presheaf C ℓA}
    {P' : Presheaf C ℓA'}
    {Q : Presheaf C ℓB}
    {Q' : Presheaf C ℓB'}
    where
    _×PshHom_ : PshHom P P' → PshHom Q Q' → PshHom (P ×Psh Q) (P' ×Psh Q')
    α ×PshHom β = ×PshIntro (π₁ P Q ⋆PshHom α) (π₂ P Q ⋆PshHom β)
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

  -- This should be possible to do compositionally if PshProd were
  -- universe polymorphic
  LRProf : (P : Presheaf C ℓP) → Profunctor C C (ℓ-max ℓ' ℓP)
  LRProf P .F-ob x = (C [-, x ]) ×Psh P
  LRProf P .F-hom f = PshHom→NatTrans (×PshIntro (π₁ _ _ ⋆PshHom yoRec _ f) (π₂ _ _))
  LRProf P .F-id = makeNatTransPath $ funExt λ y → funExt λ f → ΣPathP (C.⋆IdR _ , refl)
  LRProf P .F-seq f g = makeNatTransPath $ funExt λ y → funExt λ h →
    ΣPathP ((sym $ C.⋆Assoc (π₁ (C [-, _ ]) P .N-ob y h) f g) , refl)

  LocallyRepresentable : Presheaf C ℓP → Type _
  LocallyRepresentable P = UniversalElements $ LRProf P

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

-- Local Representability stuff
-- TODO: move to its own module probably
LRPresheaf : ∀ (C : Category ℓ ℓ') (ℓP : Level) → Type _
LRPresheaf C ℓP = Σ (Presheaf C ℓP) LocallyRepresentable

LRPsh→Functor : ∀ {C : Category ℓ ℓ'}
  ((P , _×P) : LRPresheaf C ℓP)
  → Functor C C
LRPsh→Functor (P , _×P) = FunctorComprehension (LRProf P) _×P
