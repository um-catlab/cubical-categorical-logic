{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Presheaf.KanExtension.Discrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Discrete.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex

private
  variable
    ℓI ℓD ℓD' ℓS : Level

open Category
open Functor
open NatTrans
open UnitCounit

module _ (ℓS : Level) {I : Type ℓI} (isSetI : isSet I)
  {D : Category ℓD ℓD'}
  (J : Functor (EqDiscreteCategory I isSetI) D)
  where

  private
    Disc = EqDiscreteCategory I isSetI
    module D = Category D
    ℓ = ℓ-max (ℓ-max ℓI ℓD') ℓS

  -- For a discrete indexing category, the coend defining Lan is an
  -- ordinary dependent sum: there are no nonidentity arrows to quotient by.
  LanOb : Presheaf Disc ℓ → Presheaf D ℓ
  LanOb X .F-ob d .fst =
    Σ[ i ∈ I ] Σ[ g ∈ D [ d , J .F-ob i ] ] X .F-ob i .fst
  LanOb X .F-ob d .snd =
    isSetΣ isSetI (λ i → isSetΣ (D .isSetHom)
      (λ _ → X .F-ob i .snd))
  LanOb X .F-hom h (i , g , x) = i , h D.⋆ g , x
  LanOb X .F-id = funExt λ (i , g , x) →
    ΣPathP (refl , ΣPathP (D.⋆IdL g , refl))
  LanOb X .F-seq h k = funExt λ (i , g , x) →
    ΣPathP (refl , ΣPathP (D.⋆Assoc k h g , refl))

  Lan : Functor (PresheafCategory Disc ℓ) (PresheafCategory D ℓ)
  Lan .F-ob = LanOb
  Lan .F-hom α .N-ob d (i , g , x) = i , g , α .N-ob i x
  Lan .F-hom α .N-hom h = refl
  Lan .F-id = makeNatTransPath refl
  Lan .F-seq α β = makeNatTransPath refl

  -- Dually, the end defining Ran is an ordinary dependent product; its
  -- coherence field is forced by equality elimination.
  RanOb : Presheaf Disc ℓ → Presheaf D ℓ
  RanOb X .F-ob d .fst =
    (i : I) → D [ J .F-ob i , d ] → X .F-ob i .fst
  RanOb X .F-ob d .snd = isSetΠ2 λ i _ → X .F-ob i .snd
  RanOb X .F-hom h z i g = z i (g D.⋆ h)
  RanOb X .F-id = funExt λ z → funExt λ i → funExt λ g →
    cong (z i) (D.⋆IdR g)
  RanOb X .F-seq h k = funExt λ z → funExt λ i → funExt λ g →
    cong (z i) (sym (D.⋆Assoc g k h))

  Ran : Functor (PresheafCategory Disc ℓ) (PresheafCategory D ℓ)
  Ran .F-ob = RanOb
  Ran .F-hom α .N-ob d z i g = α .N-ob i (z i g)
  Ran .F-hom α .N-hom h = refl
  Ran .F-id = makeNatTransPath refl
  Ran .F-seq α β = makeNatTransPath refl

  J* : Functor (PresheafCategory D ℓ) (PresheafCategory Disc ℓ)
  J* = reindPshF J

  module _ {X : Presheaf Disc ℓ} {Y : Presheaf D ℓ} where
    lan♭ : NatTrans (LanOb X) Y → NatTrans X (J* .F-ob Y)
    lan♭ α .N-ob i x = α .N-ob (J .F-ob i) (i , D.id , x)
    lan♭ α .N-hom Eq.refl = funExt λ x →
      cong (α .N-ob _)
        (ΣPathP (refl , ΣPathP (refl , funExt⁻ (X .F-id) x)))
      ∙ sym
          (cong (λ q → Y .F-hom q (α .N-ob _ (_ , D.id , x))) (J .F-id)
          ∙ funExt⁻ (Y .F-id) (α .N-ob _ (_ , D.id , x)))

    lan♯ : NatTrans X (J* .F-ob Y) → NatTrans (LanOb X) Y
    lan♯ β .N-ob d (i , g , x) = Y .F-hom g (β .N-ob i x)
    lan♯ β .N-hom h = funExt λ (i , g , x) →
      funExt⁻ (Y .F-seq g h) (β .N-ob i x)

    lan♭♯ : (f : NatTrans X (J* .F-ob Y)) → lan♭ (lan♯ f) ≡ f
    lan♭♯ f = makeNatTransPath (funExt λ i → funExt λ x →
      funExt⁻ (Y .F-id) (f .N-ob i x))

    lan♯♭ : (f : NatTrans (LanOb X) Y) → lan♯ (lan♭ f) ≡ f
    lan♯♭ f = makeNatTransPath (funExt λ d →
      funExt λ (i , g , x) →
        sym (funExt⁻ (f .N-hom g) (i , D.id , x))
        ∙ cong (f .N-ob d)
            (ΣPathP (refl , ΣPathP (D.⋆IdR g , refl))))

  open NaturalBijection

  Lan⊣J*-natural : Lan NaturalBijection.⊣ J*
  Lan⊣J*-natural ._⊣_.adjIso .Iso.fun = lan♭
  Lan⊣J*-natural ._⊣_.adjIso .Iso.inv = lan♯
  Lan⊣J*-natural ._⊣_.adjIso .Iso.sec = lan♭♯
  Lan⊣J*-natural ._⊣_.adjIso .Iso.ret = lan♯♭
  Lan⊣J*-natural ._⊣_.adjNatInD f k = makeNatTransPath refl
  Lan⊣J*-natural ._⊣_.adjNatInC g h = makeNatTransPath refl

  Lan⊣J* : Lan UnitCounit.⊣ J*
  Lan⊣J* = adj'→adj Lan J* Lan⊣J*-natural

  module _ {Y : Presheaf D ℓ} {X : Presheaf Disc ℓ} where
    ran♭ : NatTrans (J* .F-ob Y) X → NatTrans Y (RanOb X)
    ran♭ α .N-ob d y i g = α .N-ob i (Y .F-hom g y)
    ran♭ α .N-hom h = funExt λ y → funExt λ i → funExt λ g →
      cong (α .N-ob i) (sym (funExt⁻ (Y .F-seq h g) y))

    ran♯ : NatTrans Y (RanOb X) → NatTrans (J* .F-ob Y) X
    ran♯ β .N-ob i y = β .N-ob (J .F-ob i) y i D.id
    ran♯ β .N-hom Eq.refl = funExt λ y →
      funExt⁻ (funExt⁻ (funExt⁻ (β .N-hom (J .F-hom Eq.refl)) y) _) D.id
      ∙ cong (β .N-ob _ y _)
          (D.⋆IdL (J .F-hom Eq.refl) ∙ J .F-id)
      ∙ sym (funExt⁻ (X .F-id) (β .N-ob _ y _ D.id))

    ran♭♯ : (f : NatTrans Y (RanOb X)) → ran♭ (ran♯ f) ≡ f
    ran♭♯ f = makeNatTransPath (funExt λ d → funExt λ y →
      funExt λ i → funExt λ g →
        funExt⁻ (funExt⁻ (funExt⁻ (f .N-hom g) y) i) D.id
        ∙ cong (f .N-ob d y i) (D.⋆IdL g))

    ran♯♭ : (f : NatTrans (J* .F-ob Y) X) → ran♯ (ran♭ f) ≡ f
    ran♯♭ f = makeNatTransPath (funExt λ i → funExt λ y →
      cong (f .N-ob i) (funExt⁻ (Y .F-id) y))

  J*⊣Ran-natural : J* NaturalBijection.⊣ Ran
  J*⊣Ran-natural ._⊣_.adjIso .Iso.fun = ran♭
  J*⊣Ran-natural ._⊣_.adjIso .Iso.inv = ran♯
  J*⊣Ran-natural ._⊣_.adjIso .Iso.sec = ran♭♯
  J*⊣Ran-natural ._⊣_.adjIso .Iso.ret = ran♯♭
  J*⊣Ran-natural ._⊣_.adjNatInD f k = makeNatTransPath refl
  J*⊣Ran-natural ._⊣_.adjNatInC g h = makeNatTransPath refl

  J*⊣Ran : J* UnitCounit.⊣ Ran
  J*⊣Ran = adj'→adj J* Ran J*⊣Ran-natural
