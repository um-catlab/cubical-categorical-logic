{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Profunctor.Constructions.Composition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Homomorphism.Bilinear

private
  variable
    ℓ ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR ℓQ : Level

open Functor

module _ {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where
  private
    module B = Category B
    module C = Category C
    module D = Category D
    variable
      b b' b'' : B.ob
      c c' c'' : C.ob
      d d' d'' : D.ob
  module ⊙Defs (Q : Profunctor C B ℓQ) (R : Profunctor D C ℓR) where
    private
      module Q = ProfunctorNotation Q
      module R = ProfunctorNotation R
    ⊙ℓ = ℓ-max ℓB $ ℓ-max ℓC $ ℓ-max ℓD $ ℓ-max ℓC' $ ℓ-max ℓQ ℓR
    data ⊙Het : B.ob → D.ob
      → Type ⊙ℓ where
      _⟨⋆ᵖ⟩_ : (q : Q.Het[ b , c ])(r : R.Het[ c , d ]) → ⊙Het b d
      ⟨⋆Assocᵖᶜᵖ⟩ : (q : Q.Het[ b , c ])(g : C.Hom[ c , c' ])(r : R.Het[ c' , d ])
        → ((q Q.⋆ᵖᶜ g) ⟨⋆ᵖ⟩ r) ≡ (q ⟨⋆ᵖ⟩ (g R.⋆ᶜᵖ r))
      isSet⊙Het : isSet (⊙Het b d)
    elim : {M : ∀ {b}{d}(h : ⊙Het b d) → Type ℓ}
      → (isSetM : ∀ {b d} (h : ⊙Het b d) → isSet (M h))
      → (case-⟨⋆p⟩ : ∀ {b c d}
          (q : Q.Het[ b , c ])(r : R.Het[ c , d ])
          → M (q ⟨⋆ᵖ⟩ r))
      → (case-⟨⋆Assocᵖᶜᵖ⟩ : ∀ {b c c' d}(q : Q.Het[ b , c ])(g : C.Hom[ c , c' ])(r : R.Het[ c' , d ])
        → PathP (λ i → M (⟨⋆Assocᵖᶜᵖ⟩ q g r i))
            (case-⟨⋆p⟩ (q Q.⋆ᵖᶜ g) r)
            (case-⟨⋆p⟩ q (g R.⋆ᶜᵖ r)))
      → ∀ {b d} → (h : ⊙Het b d) → M h
    elim isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ (q ⟨⋆ᵖ⟩ r) = case-⟨⋆p⟩ q r
    elim isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ (⟨⋆Assocᵖᶜᵖ⟩ q g r i) =
      case-⟨⋆Assocᵖᶜᵖ⟩ q g r i
    elim isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ (isSet⊙Het h h' x y i j) =
      isSet→isSetDep isSetM
        (elim isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ h)
        (elim isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ h')
        (λ i → elim isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ (x i))
        (λ i → elim isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ (y i))
        (isSet⊙Het h h' x y)
        i j
    rec : {M : ∀ (b : B.ob)(d : D.ob) → Type ℓ}
      → (isSetM : ∀ {b d} → isSet (M b d))
      → (case-⟨⋆p⟩ : ∀ {b c d}
          (q : Q.Het[ b , c ])(r : R.Het[ c , d ]) → M b d)
      → (case-⟨⋆Assocᵖᶜᵖ⟩ : ∀ {b c c' d}(q : Q.Het[ b , c ])(g : C.Hom[ c , c' ])(r : R.Het[ c' , d ])
        → (case-⟨⋆p⟩ (q Q.⋆ᵖᶜ g) r) ≡ (case-⟨⋆p⟩ q (g R.⋆ᶜᵖ r)))
      → ∀ {b d} → (h : ⊙Het b d) → M b d
    rec isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ (q ⟨⋆ᵖ⟩ r) = case-⟨⋆p⟩ q r
    rec isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ (⟨⋆Assocᵖᶜᵖ⟩ q g r i) =
      case-⟨⋆Assocᵖᶜᵖ⟩ q g r i
    rec isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ (isSet⊙Het h h' x y i j) =
      isSetM (rec isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ h)
             (rec isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ h')
             (λ i → rec isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ (x i))
             (λ i → rec isSetM case-⟨⋆p⟩ case-⟨⋆Assocᵖᶜᵖ⟩ (y i))
             i j
    opaque
      ind : {M : ∀ {b}{d}(h : ⊙Het b d) → Type ℓ}
        → (isPropM : ∀ {b d} (h : ⊙Het b d) → isProp (M h))
        → (case-⟨⋆p⟩ : ∀ {b c d}
            (q : Q.Het[ b , c ])(r : R.Het[ c , d ])
            → M (q ⟨⋆ᵖ⟩ r))
        → ∀ {b d} → (h : ⊙Het b d) → M h
      ind {M = M} isPropM case-⟨⋆p⟩ h = elim
        (λ h → isProp→isSet (isPropM h))
        case-⟨⋆p⟩
        (λ _ _ _ → isProp→PathP (λ _ → isPropM _) _ _)
        h

    _⟨⋆ᵖᶜ⟩_ : (qr : ⊙Het b d) (h : D.Hom[ d , d' ])
      → ⊙Het b d'
    _⟨⋆ᵖᶜ⟩_ qr h = rec {M = M} (isSetImplicitΠ (λ _ → isSet→ isSet⊙Het))
        (λ q r h → q ⟨⋆ᵖ⟩ (r R.⋆ᵖᶜ h))
        (λ q g r → implicitFunExt $ funExt λ h →
          ⟨⋆Assocᵖᶜᵖ⟩ _ _ _
          ∙ cong (q ⟨⋆ᵖ⟩_) (sym $ R.⋆Assocᶜᵖᶜ _ _ _))
        qr
        h
        where
      M : (b : B.ob)(d : D.ob) → Type _
      M b d = ∀ {d'} (h : D.Hom[ d , d' ]) → ⊙Het b d'

    _⟨⋆ᶜᵖ⟩_ : (f : B.Hom[ b , b' ])(qr : ⊙Het b' d)
      → ⊙Het b d
    _⟨⋆ᶜᵖ⟩_ {b} {b'} {d} f qr = rec {M = M}
      (isSetImplicitΠ (λ _ → isSet→ isSet⊙Het))
      (λ q r f → (f Q.⋆ᶜᵖ q) ⟨⋆ᵖ⟩ r)
      (λ q g r → implicitFunExt $ funExt λ f →
        (cong (_⟨⋆ᵖ⟩ r) $ sym $ Q.⋆Assocᶜᵖᶜ f q g)
        ∙ ⟨⋆Assocᵖᶜᵖ⟩ _ _ _)
      qr
      f
      where
      M : (b : B.ob)(d : D.ob) → Type _
      M b d = ∀ {b'} (f : B.Hom[ b' , b ]) → ⊙Het b' d
    opaque
      ⟨⋆IdLᶜᵖ⟩ : ∀ (q⋆r : ⊙Het b d)
        → (B.id ⟨⋆ᶜᵖ⟩ q⋆r) ≡ q⋆r
      ⟨⋆IdLᶜᵖ⟩ = ind {M = M} (λ _ → isSet⊙Het _ _) λ q r →
        cong (_⟨⋆ᵖ⟩ r) (Q.⋆IdLᶜᵖ q)
        where
        M : ∀ {b}{d}(q⋆r : ⊙Het b d) → Type ⊙ℓ
        M {b} q⋆r = (B.id {b} ⟨⋆ᶜᵖ⟩ q⋆r) ≡ q⋆r
      ⟨⋆IdRᵖᶜ⟩ : ∀ (q⋆r : ⊙Het b d)
        → (q⋆r ⟨⋆ᵖᶜ⟩ D.id) ≡ q⋆r
      ⟨⋆IdRᵖᶜ⟩ = ind {M = M} (λ _ → isSet⊙Het _ _) λ q r →
        cong (q ⟨⋆ᵖ⟩_) (R.⋆IdRᵖᶜ r)
        where
        M : ∀ {b}{d}(q⋆r : ⊙Het b d) → Type ⊙ℓ
        M {b} q⋆r = (q⋆r ⟨⋆ᵖᶜ⟩ D.id) ≡ q⋆r
      ⟨⋆Assocᶜᶜᵖ⟩ :
        ∀ (f : B.Hom[ b'' , b' ])(f' : B.Hom[ b' , b ]) (q⋆r : ⊙Het b d)
        → ((f B.⋆ f') ⟨⋆ᶜᵖ⟩ q⋆r) ≡ (f ⟨⋆ᶜᵖ⟩ (f' ⟨⋆ᶜᵖ⟩ q⋆r))
      ⟨⋆Assocᶜᶜᵖ⟩ f f' q⋆r = ind {M = M} (λ q⋆r → isPropImplicitΠ2 (λ _ _ → isPropΠ2 (λ _ _ → isSet⊙Het _ _)))
        (λ q r f f' → cong (_⟨⋆ᵖ⟩ r) (Q.⋆Assocᶜᶜᵖ _ _ _))
        q⋆r f f' where
        M : ∀ {b}{d}(q⋆r : ⊙Het b d) → Type (ℓ-max ℓB' ⊙ℓ)
        M {b}{d} q⋆r = ∀ {b''}{b'}(f : B.Hom[ b'' , b' ])(f' : B.Hom[ b' , b ]) → ((f B.⋆ f') ⟨⋆ᶜᵖ⟩ q⋆r) ≡ (f ⟨⋆ᶜᵖ⟩ (f' ⟨⋆ᶜᵖ⟩ q⋆r))

      ⟨⋆Assocᵖᶜᶜ⟩ : ∀ (q⋆r : ⊙Het b d)(h : D.Hom[ d , d' ])(h' : D.Hom[ d' , d'' ])
        → (q⋆r ⟨⋆ᵖᶜ⟩ (h D.⋆ h')) ≡ ((q⋆r ⟨⋆ᵖᶜ⟩ h) ⟨⋆ᵖᶜ⟩ h')
      ⟨⋆Assocᵖᶜᶜ⟩ q⋆r h h' = ind {M = M} ((λ q⋆r → isPropImplicitΠ2 (λ _ _ → isPropΠ2 (λ _ _ → isSet⊙Het _ _))))
        (λ q r h h' → cong (q ⟨⋆ᵖ⟩_) (sym $ (R.⋆Assocᵖᶜᶜ _ _ _)))
        q⋆r h h' where
        M : ∀ {b}{d}(q⋆r : ⊙Het b d) → Type (ℓ-max ℓD' ⊙ℓ)
        M {b}{d} q⋆r = ∀ {d'}{d''}(h : D.Hom[ d , d' ])(h' : D.Hom[ d' , d'' ])
         → (q⋆r ⟨⋆ᵖᶜ⟩ (h D.⋆ h')) ≡ ((q⋆r ⟨⋆ᵖᶜ⟩ h) ⟨⋆ᵖᶜ⟩ h')
      ⟨⋆Assocᶜᵖᶜ⟩ : ∀ (f : B.Hom[ b' , b ])(q⋆r : ⊙Het b d)(h : D.Hom[ d , d' ]) → (f ⟨⋆ᶜᵖ⟩ (q⋆r ⟨⋆ᵖᶜ⟩ h)) ≡ ((f ⟨⋆ᶜᵖ⟩ q⋆r) ⟨⋆ᵖᶜ⟩ h)
      ⟨⋆Assocᶜᵖᶜ⟩ f q⋆r h = ind {M = M} (λ q⋆r → isPropImplicitΠ2 (λ _ _ → isPropΠ2 (λ _ _ → isSet⊙Het _ _)))
        (λ q r f h → refl)
        q⋆r f h where
        M : ∀ {b}{d}(q⋆r : ⊙Het b d) → Type (ℓ-max (ℓ-max ℓB' ℓD') ⊙ℓ)
        M {b}{d} q⋆r = ∀ {b'}{d'}(f : B.Hom[ b' , b ])(h : D.Hom[ d , d' ]) → (f ⟨⋆ᶜᵖ⟩ (q⋆r ⟨⋆ᵖᶜ⟩ h)) ≡ ((f ⟨⋆ᶜᵖ⟩ q⋆r) ⟨⋆ᵖᶜ⟩ h)
  _⊙_ : (Q : Profunctor C B ℓQ) (R : Profunctor D C ℓR) → Profunctor D B _
  (Q ⊙ R) = CurryBifunctor $ Sym $ mkBifunctorSep Q⊙R where
    open BifunctorSep
    open ⊙Defs Q R
    Q⊙R : BifunctorSep (B ^op) D (SET _)
    Q⊙R .Bif-ob b d .fst = ⊙Het b d
    Q⊙R .Bif-ob b d .snd = isSet⊙Het
    Q⊙R .Bif-homL f d q⋆r = f ⟨⋆ᶜᵖ⟩ q⋆r
    Q⊙R .Bif-homR c h q⋆r = q⋆r ⟨⋆ᵖᶜ⟩ h
    Q⊙R .Bif-L-id = funExt λ q⋆r → ⟨⋆IdLᶜᵖ⟩ q⋆r
    Q⊙R .Bif-L-seq f' f = funExt λ q⋆r → ⟨⋆Assocᶜᶜᵖ⟩ f f' q⋆r
    Q⊙R .Bif-R-id = funExt λ q⋆r → ⟨⋆IdRᵖᶜ⟩ q⋆r
    Q⊙R .Bif-R-seq h h' = funExt λ q⋆r → ⟨⋆Assocᵖᶜᶜ⟩ q⋆r h h'
    Q⊙R .SepBif-RL-commute f h = funExt λ q⋆r → ⟨⋆Assocᶜᵖᶜ⟩ f q⋆r h
  ⊙-σ : (Q : Profunctor C B ℓQ) (R : Profunctor D C ℓR) → Bilinear Q R (Q ⊙ R)
  ⊙-σ Q R .Bilinear._⋆ᵖ_ = ⊙Defs._⟨⋆ᵖ⟩_
  ⊙-σ Q R .Bilinear.⋆Assocᶜᵖᵖ f q r = refl
  ⊙-σ Q R .Bilinear.⋆Assocᵖᶜᵖ q g r = ⊙Defs.⟨⋆Assocᵖᶜᵖ⟩ q g r
  ⊙-σ Q R .Bilinear.⋆Assocᵖᵖᶜ q r h = refl

  -- TODO: universe polymorphic ProfunctorHom
  -- ⊙-rec : (Q : Profunctor C B ℓQ) (R : Profunctor D C ℓR) (S : Profunctor D B ℓS)
  --   → (α : Bilinear Q R S)
  --   → NatTrans {!Q ⊙ R!} S
  -- ⊙-rec = {!!}
