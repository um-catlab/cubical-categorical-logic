{-# OPTIONS --lossy-unification #-}
module Gluing.BiCartesianClosedCategory.BoolNatCanonicity.Base where

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

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Displayed.Instances.Weaken.UncurriedProperties
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Base
import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.UncurriedElim
  as FreeBiCCC
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver

open import Gluing.Canonicity

open Category
open Functor

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
    module FREEBICCC = BiCartesianClosedCategory
      (FreeBiCartesianClosedCategory +×⇒QUIVER)

  [bool] : Type _
  [bool] = FREEBICCC.Hom[ ⊤ , ↑ bool ]

  [t] [f] : [bool]
  [t] = ↑ₑ tr
  [f] = ↑ₑ fl

  [nat] : Type _
  [nat] = FREEBICCC.Hom[ ⊤ , ↑ nat ]

  [ze] : [nat]
  [ze] = ↑ₑ ze

  [su] : FREEBICCC.Hom[ ↑ nat , ↑ nat ]
  [su] = ↑ₑ su

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
    S : Section (FREEBICCC.C [ ⊤ ,-]) (SETᴰ ℓ-zero ℓ-zero)
    S = FreeBiCCC.elimLocal +×⇒QUIVER
      (CorepCartesian FREEBICCC.CC ⊤)
      EqSETᴰBCCCⱽ (FreeBiCCC.interpᴰ
      (λ { bool e → CanonicalFormBool e ; nat e → CanonicalFormNat e })
      λ { tr e _ → inl (cong₂ _⋆ₑ_ (⊤→⊤IsId FREEBICCC.term e) refl
                        ∙ FREEBICCC.⋆IdL _)
        ; fl e _ → inr (cong₂ _⋆ₑ_ (⊤→⊤IsId FREEBICCC.term e) refl
                        ∙ FREEBICCC.⋆IdL _)
        ; ze e _ → 0 , (sym (cong₂ _⋆ₑ_ (⊤→⊤IsId FREEBICCC.term e) refl
                             ∙ FREEBICCC.⋆IdL _))
        ; su e (n , fib) → (suc n) , cong₂ _⋆ₑ_ fib refl
        })

  ⟦-⟧SET : Functor FREEBICCC.C (SET ℓ-zero)
  ⟦-⟧SET = FreeBiCCC.rec +×⇒QUIVER SETBiCCC (FreeBiCCC.interpᴰ
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
    (λ e → canonicalize ⊤ S _ e)

  canonicity-nat : Iso [nat] ℕ
  canonicity-nat = NatIso.canonicity-nat ＂_＂ evalNat evalNat-＂_＂
    (λ e → canonicalize ⊤ S _ e)

  -- === Product Canonicity ===
  canonicity-× :
    Iso (FREEBICCC.Hom[ ⊤ , (↑ bool) × (↑ nat) ])
        (Bool Sigma.× ℕ)
  canonicity-× = CanonicalFormIso.canonicity
    inv×
    (λ e → ⟦-⟧SET .F-hom e tt*)
    (λ { (b , n) →
      ΣPathP (canonicity-bool .Iso.sec b ,
              canonicity-nat .Iso.sec n) })
    (λ e →
      (evalBool (e ⋆ₑ π₁) ,
       evalNat (e ⋆ₑ π₂)) ,
      cong₂ ⟨_,_⟩
        (canonicity-bool .Iso.ret (e ⋆ₑ π₁))
        (canonicity-nat .Iso.ret (e ⋆ₑ π₂))
      ∙ sym ×η)
    where
    inv× : Bool Sigma.× ℕ
      → FREEBICCC.Hom[ ⊤ , (↑ bool) × (↑ nat) ]
    inv× (b , n) =
      ⟨ canonicity-bool .Iso.inv b ,
        canonicity-nat .Iso.inv n ⟩

  private
    inj₁' : Expr +×⇒QUIVER (↑ bool) ((↑ bool) + (↑ nat))
    inj₁' = σ₁

    inj₂' : Expr +×⇒QUIVER (↑ nat) ((↑ bool) + (↑ nat))
    inj₂' = σ₂

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
    (λ e → Sum.elim
      {C = λ _ → fiber inv+ e}
      (λ { (y , q , _) → inl (evalBool y) ,
        cong (_⋆ₑ inj₁')
          (canonicity-bool .Iso.ret y) ∙ q })
      (λ { (y , q , _) → inr (evalNat y) ,
        cong (_⋆ₑ inj₂')
          (canonicity-nat .Iso.ret y) ∙ q })
      (canonicalize ⊤ S _ e))
    where
    inv+ : Bool ⊎ ℕ
      → FREEBICCC.Hom[ ⊤ , (↑ bool) + (↑ nat) ]
    inv+ (inl b) =
      canonicity-bool .Iso.inv b ⋆ₑ inj₁'
    inv+ (inr n) =
      canonicity-nat .Iso.inv n ⋆ₑ inj₂'

  -- === Function Canonicity ===
  private
    π₂P : Expr +×⇒QUIVER (⊤ × (⊤ + ⊤)) (⊤ + ⊤)
    π₂P = π₂

    π₁P : Expr +×⇒QUIVER (⊤ × (⊤ + ⊤)) ⊤
    π₁P = π₁

    sec⇒ : Expr +×⇒QUIVER (⊤ + ⊤) (⊤ × (⊤ + ⊤))
    sec⇒ = ⟨ !ₑ , idₑ ⟩

    uncurry' : FREEBICCC.Hom[ ⊤ , (⊤ + ⊤) ⇒ (↑ nat) ]
      → Expr +×⇒QUIVER (⊤ × (⊤ + ⊤)) (↑ nat)
    uncurry' e = ⟨ π₁P ⋆ₑ e , π₂P ⟩ ⋆ₑ eval

    to-sum : FREEBICCC.Hom[ ⊤ , (⊤ + ⊤) ⇒ (↑ nat) ]
      → FREEBICCC.Hom[ ⊤ + ⊤ , ↑ nat ]
    to-sum e =
      (sec⇒ ⋆ₑ ⟨ π₁P ⋆ₑ e , π₂P ⟩) ⋆ₑ eval

    from-sum : FREEBICCC.Hom[ ⊤ + ⊤ , ↑ nat ]
      → FREEBICCC.Hom[ ⊤ , (⊤ + ⊤) ⇒ (↑ nat) ]
    from-sum f = λ- (π₂P ⋆ₑ f)

    curry-sec : ∀ f → to-sum (from-sum f) ≡ f
    curry-sec f =
      ⋆ₑAssoc sec⇒
        (⟨ π₁P ⋆ₑ (λ- (π₂P ⋆ₑ f)) , π₂P ⟩) eval
      ∙ cong (λ (x : Expr +×⇒QUIVER
                   (⊤ × (⊤ + ⊤)) (↑ nat))
                → sec⇒ ⋆ₑ x)
             (λβ (π₂P ⋆ₑ f))
      ∙ sym (⋆ₑAssoc sec⇒ π₂P f)
      ∙ cong (_⋆ₑ f) ×β₂
      ∙ ⋆ₑIdL f

    π₂⋆sec⇒≡id : π₂P ⋆ₑ sec⇒ ≡ idₑ
    π₂⋆sec⇒≡id =
      ×η
      ∙ cong₂ ⟨_,_⟩ comp₁ comp₂
      ∙ sym ×η
      where
      comp₁ : (π₂P ⋆ₑ sec⇒) ⋆ₑ π₁P
        ≡ idₑ ⋆ₑ π₁P
      comp₁ =
        ⋆ₑAssoc π₂P sec⇒ π₁P
        ∙ cong (λ (x : Expr +×⇒QUIVER
                     (⊤ + ⊤) ⊤) → π₂P ⋆ₑ x) ×β₁
        ∙ ⊤η (π₂P ⋆ₑ !ₑ)
        ∙ sym (⊤η (idₑ ⋆ₑ π₁P))

      comp₂ : (π₂P ⋆ₑ sec⇒) ⋆ₑ π₂P
        ≡ idₑ ⋆ₑ π₂P
      comp₂ =
        ⋆ₑAssoc π₂P sec⇒ π₂P
        ∙ cong (λ (x : Expr +×⇒QUIVER
                     (⊤ + ⊤) (⊤ + ⊤))
                  → π₂P ⋆ₑ x) ×β₂
        ∙ ⋆ₑIdR π₂P
        ∙ sym (⋆ₑIdL π₂P)

    curry-ret : ∀ e → from-sum (to-sum e) ≡ e
    curry-ret e =
      cong (λ-_)
        (cong (λ (x : Expr +×⇒QUIVER
                    (⊤ + ⊤) (↑ nat)) → π₂P ⋆ₑ x)
              (⋆ₑAssoc sec⇒
                (⟨ π₁P ⋆ₑ e , π₂P ⟩) eval)
         ∙ sym (⋆ₑAssoc π₂P sec⇒ (uncurry' e))
         ∙ cong (_⋆ₑ uncurry' e) π₂⋆sec⇒≡id
         ∙ ⋆ₑIdL (uncurry' e))
      ∙ sym (λη e)

  -- Using canonicity we can get a baby version of normalization
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
      (evalNat (σ₁ {Γ = ⊤} {Δ = ⊤} ⋆ₑ to-sum e) ,
       evalNat (σ₂ {Γ = ⊤} {Δ = ⊤} ⋆ₑ to-sum e)) ,
      cong (λ (f : Expr +×⇒QUIVER
                     (⊤ + ⊤) (↑ nat))
              → λ- (π₂P ⋆ₑ f))
        (cong₂ [_,_]
          (canonicity-nat .Iso.ret
            (σ₁ {Γ = ⊤} {Δ = ⊤} ⋆ₑ to-sum e))
          (canonicity-nat .Iso.ret
            (σ₂ {Γ = ⊤} {Δ = ⊤} ⋆ₑ to-sum e))
        ∙ sym +η)
      ∙ curry-ret e)
    where
    inv⇒ : ℕ Sigma.× ℕ
      → FREEBICCC.Hom[ ⊤ , (⊤ + ⊤) ⇒ (↑ nat) ]
    inv⇒ (m , n) =
      λ- (π₂P ⋆ₑ [ ＂ m ＂ , ＂ n ＂ ])
