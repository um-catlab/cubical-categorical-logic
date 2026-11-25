{-# OPTIONS --lossy-unification #-}
module Gluing.BiCartesianClosedCategory.BoolNatCanonicity.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure hiding (⟨_⟩)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum.Properties
open import Cubical.Data.Unit
open import Cubical.Data.Sigma as Sigma hiding (_×_)
open import Cubical.Data.Quiver.Base
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Displayed.Instances.Weaken.UncurriedProperties
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Sets
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Forded as FreeBiCCC
  renaming ([_,_] to [_,+_])
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver

open import Gluing.Canonicity

open Category
open Functor
open Section

module _ where
  data OB : Type where
    bool nat : OB

  data MOR : Type ℓ-zero where
    tr fl ze su : MOR

  open QuiverOver

  +×⇒QUIVER : +×⇒Quiver ℓ-zero ℓ-zero
  +×⇒QUIVER .+×⇒Quiver.ob = OB
  +×⇒QUIVER .+×⇒Quiver.Q .mor = MOR
  +×⇒QUIVER .+×⇒Quiver.Q .dom tr = ⊤
  +×⇒QUIVER .+×⇒Quiver.Q .dom fl = ⊤
  +×⇒QUIVER .+×⇒Quiver.Q .dom ze = ⊤
  +×⇒QUIVER .+×⇒Quiver.Q .dom su = ↑ nat
  +×⇒QUIVER .+×⇒Quiver.Q .cod tr = ↑ bool
  +×⇒QUIVER .+×⇒Quiver.Q .cod fl = ↑ bool
  +×⇒QUIVER .+×⇒Quiver.Q .cod ze = ↑ nat
  +×⇒QUIVER .+×⇒Quiver.Q .cod su = ↑ nat

  private
    module FREEBICCC = BiCartesianClosedCategory (FreeBiCartesianClosedCategory +×⇒QUIVER)

  [bool] : Type _
  [bool] = FREEBICCC.Hom[ ⊤ , ↑ bool ]

  [t] [f] : [bool]
  [t] = ↑ₑ +×⇒QUIVER tr
  [f] = ↑ₑ +×⇒QUIVER fl

  [nat] : Type _
  [nat] = FREEBICCC.Hom[ ⊤ , ↑ nat ]

  [ze] : [nat]
  [ze] = ↑ₑ +×⇒QUIVER ze

  [su] : FREEBICCC.Hom[ ↑ nat , ↑ nat ]
  [su] = ↑ₑ +×⇒QUIVER su

  ＂_＂ : ℕ → [nat]
  ＂ zero ＂ = [ze]
  ＂ suc n ＂ = ＂ n ＂ ⋆ₑ [su]

  CanonicalFormBool : [bool] → hSet ℓ-zero
  CanonicalFormBool e =
    ((e ≡ [t]) ⊎ (e ≡ [f])) ,
    isSet⊎ (isProp→isSet (FREEBICCC.isSetHom _ _))
           (isProp→isSet (FREEBICCC.isSetHom _ _))

  CanonicalFormNat : [nat] → hSet ℓ-zero
  CanonicalFormNat e =
    fiber ＂_＂ e ,
    isSetΣ isSetℕ (λ _ → isProp→isSet (FREEBICCC.isSetHom _ _))

  private
    constOnTop : ∀ {o} (e : FREEBICCC.Hom[ ⊤ , ⊤ ]) (g : FREEBICCC.Hom[ ⊤ , o ])
      → e ⋆ₑ g ≡ g
    constOnTop e g =
      cong₂ _⋆ₑ_ (⊤→⊤IsId FREEBICCC.term e) refl ∙ FREEBICCC.⋆IdL _

  S : Section (FREEBICCC.C [ ⊤ ,-]) (SETCod ℓ-zero)
  S = FreeBiCCC.elimLocal +×⇒QUIVER
    (CorepCartesian FREEBICCC.CC ⊤)
    SETCodBCCCⱽ (mkElimInterpᴰ
    (λ { bool → CanonicalFormBool ; nat → CanonicalFormNat })
    λ { tr → mk ℓ-zero λ z → (_ , inl (constOnTop (z .fst) [t])) , refl
      ; fl → mk ℓ-zero λ z → (_ , inr (constOnTop (z .fst) [f])) , refl
      ; ze → mk ℓ-zero λ z →
          (_ , 0 , sym (constOnTop (z .fst) [ze])) , refl
      ; su → mk ℓ-zero λ z →
          (_ , suc (z .snd .fst) , cong₂ _⋆ₑ_ (z .snd .snd) refl) , refl
      })

  can : ∀ {o} (e : FREEBICCC.Hom[ ⊤ , o ])
    → Fib ℓ-zero {Y = (FREEBICCC.C [ ⊤ ,-]) ⟅ o ⟆} (S .F-obᴰ o) e
  can = canonicalize ⊤ S tt*

  ⟦-⟧SET : Functor FREEBICCC.C (SET ℓ-zero)
  ⟦-⟧SET = FreeBiCCC.rec +×⇒QUIVER SETBiCCC (mkElimInterpᴰ
    (λ { bool → Bool , isSetBool ; nat → ℕ , isSetℕ })
    λ { tr → λ _ → true ; fl → λ _ → false
      ; ze → λ _ → 0 ; su → suc })

  evalBool : [bool] → Bool
  evalBool e = ⟦-⟧SET .F-hom e tt*

  evalNat : [nat] → ℕ
  evalNat e = ⟦-⟧SET .F-hom e tt*

  evalNat-＂_＂ : ∀ n → evalNat ＂ n ＂ ≡ n
  evalNat-＂_＂ zero = refl
  evalNat-＂_＂ (suc n) = cong suc (evalNat-＂_＂ n)

  canonicity-bool : Iso [bool] Bool
  canonicity-bool = BoolIso.canonicity-bool [t] [f] evalBool refl refl
    (λ e → Fib→⊎ (can e))

  canonicity-nat : Iso [nat] ℕ
  canonicity-nat = NatIso.canonicity-nat ＂_＂ evalNat evalNat-＂_＂
    (λ e → Fib→fiber ＂_＂ (can e))

  private
    pair' : ∀ {Γ Δ Δ'} → Expr +×⇒QUIVER Γ Δ
      → Expr +×⇒QUIVER Γ Δ'
      → Expr +×⇒QUIVER Γ (Δ × Δ')
    pair' e₁ e₂ = ⟨ e₁ , e₂ ⟩ Eq.refl

    proj₁' : ∀ {Γ Δ} → Expr +×⇒QUIVER (Γ × Δ) Γ
    proj₁' = π₁ Eq.refl Eq.refl

    proj₂' : ∀ {Γ Δ} → Expr +×⇒QUIVER (Γ × Δ) Δ
    proj₂' = π₂ Eq.refl Eq.refl

    inj₁' : ∀ {Γ Δ} → Expr +×⇒QUIVER Γ (Γ + Δ)
    inj₁' = σ₁ Eq.refl Eq.refl

    inj₂' : ∀ {Γ Δ} → Expr +×⇒QUIVER Δ (Γ + Δ)
    inj₂' = σ₂ Eq.refl Eq.refl

    case' : ∀ {Γ Δ Δ'} → Expr +×⇒QUIVER Δ Γ
      → Expr +×⇒QUIVER Δ' Γ
      → Expr +×⇒QUIVER (Δ + Δ') Γ
    case' f g = [ f ,+ g ] Eq.refl

    Lam : ∀ {Γ Δ Θ} → Expr +×⇒QUIVER (Γ × Δ) Θ
      → Expr +×⇒QUIVER Γ (Δ ⇒ Θ)
    Lam t = lam t Eq.refl

    App : ∀ {Δ Θ} → Expr +×⇒QUIVER ((Δ ⇒ Θ) × Δ) Θ
    App = eval Eq.refl Eq.refl

  -- === Product Canonicity ===
  canonicity-× :
    Iso (FREEBICCC.Hom[ ⊤ , (↑ bool) × (↑ nat) ])
        (Bool Sigma.× ℕ)
  canonicity-× = CanonicalFormIso.canonicity
    inv×
    (λ e → ⟦-⟧SET .F-hom e tt*)
    (λ { (b , n) →
      ΣPathP {B = λ _ _ → ℕ} (canonicity-bool .Iso.sec b ,
              canonicity-nat .Iso.sec n) })
    (λ e →
      (evalBool (e ⋆ₑ proj₁') ,
       evalNat (e ⋆ₑ proj₂')) ,
      cong₂ pair'
        (canonicity-bool .Iso.ret (e ⋆ₑ proj₁'))
        (canonicity-nat .Iso.ret (e ⋆ₑ proj₂'))
      ∙ sym (×η Eq.refl e))
    where
    inv× : Bool Sigma.× ℕ
      → FREEBICCC.Hom[ ⊤ , (↑ bool) × (↑ nat) ]
    inv× (b , n) =
      pair' (canonicity-bool .Iso.inv b)
            (canonicity-nat .Iso.inv n)

  -- === Sum Canonicity ===
  canonicity-+ :
    Iso (FREEBICCC.Hom[ ⊤ , (↑ bool) + (↑ nat) ])
        (Bool ⊎ ℕ)
  canonicity-+ = CanonicalFormIso.canonicity
    inv+
    (λ e → ⟦-⟧SET .F-hom e tt*)
    (λ { (inl b) →
           cong inl (canonicity-bool .Iso.sec b)
       ; (inr n) →
           cong inr (canonicity-nat .Iso.sec n) })
    (λ e → step e (can e))
    where
    inv+ : Bool ⊎ ℕ
      → FREEBICCC.Hom[ ⊤ , (↑ bool) + (↑ nat) ]
    inv+ (inl b) =
      canonicity-bool .Iso.inv b ⋆ₑ inj₁'
    inv+ (inr n) =
      canonicity-nat .Iso.inv n ⋆ₑ inj₂'

    step : ∀ e → Fib ℓ-zero (S .F-obᴰ ((↑ bool) + (↑ nat))) e → fiber inv+ e
    step e ((_ , inl ((y , _) , q)) , p) = inl (evalBool y) ,
      cong (_⋆ₑ inj₁') (canonicity-bool .Iso.ret y) ∙ q ∙ p
    step e ((_ , inr ((y , _) , q)) , p) = inr (evalNat y) ,
      cong (_⋆ₑ inj₂') (canonicity-nat .Iso.ret y) ∙ q ∙ p

  -- === Function Canonicity ===
  private
    π₂P : Expr +×⇒QUIVER (⊤ × (⊤ + ⊤)) (⊤ + ⊤)
    π₂P = proj₂'

    π₁P : Expr +×⇒QUIVER (⊤ × (⊤ + ⊤)) ⊤
    π₁P = proj₁'

    sec⇒ : Expr +×⇒QUIVER (⊤ + ⊤) (⊤ × (⊤ + ⊤))
    sec⇒ = pair' (!ₑ Eq.refl) (idₑ Eq.refl)

    uncurry' : FREEBICCC.Hom[ ⊤ , (⊤ + ⊤) ⇒ (↑ nat) ]
      → Expr +×⇒QUIVER (⊤ × (⊤ + ⊤)) (↑ nat)
    uncurry' e = pair' (π₁P ⋆ₑ e) π₂P ⋆ₑ App

    to-sum : FREEBICCC.Hom[ ⊤ , (⊤ + ⊤) ⇒ (↑ nat) ]
      → FREEBICCC.Hom[ ⊤ + ⊤ , ↑ nat ]
    to-sum e =
      (sec⇒ ⋆ₑ pair' (π₁P ⋆ₑ e) π₂P) ⋆ₑ App

    from-sum : FREEBICCC.Hom[ ⊤ + ⊤ , ↑ nat ]
      → FREEBICCC.Hom[ ⊤ , (⊤ + ⊤) ⇒ (↑ nat) ]
    from-sum f = Lam (π₂P ⋆ₑ f)

    curry-sec : ∀ f → to-sum (from-sum f) ≡ f
    curry-sec f =
      ⋆ₑAssoc sec⇒
        (pair' (π₁P ⋆ₑ Lam (π₂P ⋆ₑ f)) π₂P) App
      ∙ cong (λ (x : Expr +×⇒QUIVER
                   (⊤ × (⊤ + ⊤)) (↑ nat))
                → sec⇒ ⋆ₑ x)
             (λβ Eq.refl (π₂P ⋆ₑ f))
      ∙ sym (⋆ₑAssoc sec⇒ π₂P f)
      ∙ cong (_⋆ₑ f) ×β₂
      ∙ ⋆ₑIdL f

    π₂⋆sec⇒≡id : π₂P ⋆ₑ sec⇒ ≡ idₑ Eq.refl
    π₂⋆sec⇒≡id =
      ×η Eq.refl (π₂P ⋆ₑ sec⇒)
      ∙ cong₂ pair' comp₁ comp₂
      ∙ sym (×η Eq.refl (idₑ Eq.refl))
      where
      comp₁ : (π₂P ⋆ₑ sec⇒) ⋆ₑ π₁P
        ≡ idₑ Eq.refl ⋆ₑ π₁P
      comp₁ =
        ⋆ₑAssoc π₂P sec⇒ π₁P
        ∙ cong (λ (x : Expr +×⇒QUIVER
                     (⊤ + ⊤) ⊤) → π₂P ⋆ₑ x) ×β₁
        ∙ ⊤η Eq.refl (π₂P ⋆ₑ !ₑ Eq.refl)
        ∙ sym (⊤η Eq.refl
                 (idₑ Eq.refl ⋆ₑ π₁P))

      comp₂ : (π₂P ⋆ₑ sec⇒) ⋆ₑ π₂P
        ≡ idₑ Eq.refl ⋆ₑ π₂P
      comp₂ =
        ⋆ₑAssoc π₂P sec⇒ π₂P
        ∙ cong (λ (x : Expr +×⇒QUIVER
                     (⊤ + ⊤) (⊤ + ⊤))
                  → π₂P ⋆ₑ x) ×β₂
        ∙ ⋆ₑIdR π₂P
        ∙ sym (⋆ₑIdL π₂P)

    curry-ret : ∀ e → from-sum (to-sum e) ≡ e
    curry-ret e =
      cong Lam
        (cong (λ (x : Expr +×⇒QUIVER
                    (⊤ + ⊤) (↑ nat)) → π₂P ⋆ₑ x)
              (⋆ₑAssoc sec⇒
                (pair' (π₁P ⋆ₑ e) π₂P) App)
         ∙ sym (⋆ₑAssoc π₂P sec⇒ (uncurry' e))
         ∙ cong (_⋆ₑ uncurry' e) π₂⋆sec⇒≡id
         ∙ ⋆ₑIdL (uncurry' e))
      ∙ sym (λη Eq.refl e)

  -- Using canonicity we can get a baby version of normalzation
  -- for any fixed domain and codomain
  ⊤+⊤→nat-normalize :
    Iso (FREEBICCC.Hom[ ⊤ , (⊤ + ⊤) ⇒ (↑ nat) ])
        (ℕ Sigma.× ℕ)
  ⊤+⊤→nat-normalize = CanonicalFormIso.canonicity
    inv⇒
    (λ e → ⟦-⟧SET .F-hom e tt* (inl tt*) ,
            ⟦-⟧SET .F-hom e tt* (inr tt*))
    (λ { (m , n) →
      ΣPathP (evalNat-＂ m ＂ , evalNat-＂ n ＂) })
    (λ e →
      (evalNat (inj₁' ⋆ₑ to-sum e) ,
       evalNat (inj₂' ⋆ₑ to-sum e)) ,
      cong (λ (f : Expr +×⇒QUIVER
                     (⊤ + ⊤) (↑ nat))
              → Lam (π₂P ⋆ₑ f))
        (cong₂ case'
          (canonicity-nat .Iso.ret
            (inj₁' ⋆ₑ to-sum e))
          (canonicity-nat .Iso.ret
            (inj₂' ⋆ₑ to-sum e))
        ∙ sym (+η Eq.refl (to-sum e)))
      ∙ curry-ret e)
    where
    inv⇒ : ℕ Sigma.× ℕ
      → FREEBICCC.Hom[ ⊤ , (⊤ + ⊤) ⇒ (↑ nat) ]
    inv⇒ (m , n) =
      Lam (π₂P ⋆ₑ case' ＂ m ＂ ＂ n ＂)

  private
    module Examples where
      canonNat : [nat] → ℕ
      canonNat e = can e .fst .snd .fst

      isInl : ∀ {ℓa ℓb} {X : Type ℓa} {Y : Type ℓb} → X ⊎ Y → Bool
      isInl (inl _) = true
      isInl (inr _) = false

      canonBool : [bool] → Bool
      canonBool e = isInl (can e .fst .snd)

      canonSum : FREEBICCC.Hom[ ⊤ , (↑ bool) + (↑ nat) ] → Bool ⊎ ℕ
      canonSum e = step (can e .fst .snd)
        where
        step : _ → Bool ⊎ ℕ
        step (inl ((y , _) , _)) = inl (canonBool y)
        step (inr ((y , _) , _)) = inr (canonNat y)

      app : ∀ {Γ A B} → Expr +×⇒QUIVER Γ (A ⇒ B) → Expr +×⇒QUIVER Γ A
        → Expr +×⇒QUIVER Γ B
      app f a = pair' f a ⋆ₑ App

      sucF : Expr +×⇒QUIVER ⊤ ((↑ nat) ⇒ (↑ nat))
      sucF = Lam (proj₂' ⋆ₑ [su])

      notB : Expr +×⇒QUIVER ((↑ bool) + (↑ bool)) (↑ bool)
      notB = case' (!ₑ Eq.refl ⋆ₑ [f]) (!ₑ Eq.refl ⋆ₑ [t])

      _ : canonNat (app sucF ＂ 2 ＂) ≡ 3
      _ = refl

      _ : canonBool (([t] ⋆ₑ inj₁') ⋆ₑ notB) ≡ false
      _ = refl

      _ : canonSum (app sucF ＂ 1 ＂ ⋆ₑ inj₂') ≡ inr 2
      _ = refl
