{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianCategory.BoolNatCanonicity.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
open import Cubical.Data.Quiver.Base
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Sets

open import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Instances.Free.CartesianCategory.Forded as FreeCC

open import Gluing.Canonicity

open Category
open Functor
open Section
open QuiverOver

module _ where
  data OB : Type where
    bool nat : OB

  data MOR : Type ℓ-zero where
    tr fl ze su : MOR

  ×QUIVER : ×Quiver ℓ-zero ℓ-zero
  ×QUIVER .×Quiver.ob = OB
  ×QUIVER .×Quiver.Q .mor = MOR
  ×QUIVER .×Quiver.Q .dom tr = ⊤
  ×QUIVER .×Quiver.Q .dom fl = ⊤
  ×QUIVER .×Quiver.Q .dom ze = ⊤
  ×QUIVER .×Quiver.Q .dom su = ↑ nat
  ×QUIVER .×Quiver.Q .cod tr = ↑ bool
  ×QUIVER .×Quiver.Q .cod fl = ↑ bool
  ×QUIVER .×Quiver.Q .cod ze = ↑ nat
  ×QUIVER .×Quiver.Q .cod su = ↑ nat

  private
    FREECC = FreeCartesianCategory ×QUIVER
    module FREECC = CartesianCategory FREECC

  [bool] : Type _
  [bool] = FREECC.Hom[ ⊤ , ↑ bool ]

  [t] [f] : [bool]
  [t] = ↑ₑ ×QUIVER tr
  [f] = ↑ₑ ×QUIVER fl

  [nat] : Type _
  [nat] = FREECC.Hom[ ⊤ , ↑ nat ]

  [ze] : [nat]
  [ze] = ↑ₑ ×QUIVER ze

  [su] : FREECC.Hom[ ↑ nat , ↑ nat ]
  [su] = ↑ₑ ×QUIVER su

  ＂_＂ : ℕ → [nat]
  ＂ zero ＂ = [ze]
  ＂ suc n ＂ = ＂ n ＂ ⋆ₑ [su]

  CanonicalFormBool : [bool] → hSet ℓ-zero
  CanonicalFormBool e =
    ((e ≡ [t]) ⊎ (e ≡ [f])) ,
    isSet⊎ (isProp→isSet (FREECC.isSetHom _ _))
           (isProp→isSet (FREECC.isSetHom _ _))

  CanonicalFormNat : [nat] → hSet ℓ-zero
  CanonicalFormNat e =
    fiber ＂_＂ e ,
    isSetΣ isSetℕ (λ _ → isProp→isSet (FREECC.isSetHom _ _))

  Pts : Functor FREECC.C (SET ℓ-zero)
  Pts = FREECC.C [ ⊤ ,-]

  private

    constOnTop : ∀ {o} (e : FREECC.Hom[ ⊤ , ⊤ ]) (g : FREECC.Hom[ ⊤ , o ])
      → e ⋆ₑ g ≡ g
    constOnTop e g =
      cong₂ _⋆ₑ_ (⊤→⊤IsId FREECC.term e) refl ∙ FREECC.⋆IdL _

  S : Section Pts (SETCod ℓ-zero)
  S = FreeCC.elimLocal ×QUIVER Pts SETCodCCⱽ (mkElimInterpᴰ
    (λ { bool → CanonicalFormBool ; nat → CanonicalFormNat })
    λ { tr → mk ℓ-zero λ z → (_ , inl (constOnTop (z .fst) [t])) , refl
      ; fl → mk ℓ-zero λ z → (_ , inr (constOnTop (z .fst) [f])) , refl
      ; ze → mk ℓ-zero λ z →
          (_ , 0 , sym (constOnTop (z .fst) [ze])) , refl
      ; su → mk ℓ-zero λ z →
          (_ , suc (z .snd .fst) , cong₂ _⋆ₑ_ (z .snd .snd) refl) , refl
      })

  can : ∀ {o} (e : FREECC.Hom[ ⊤ , o ])
    → Fib ℓ-zero {Y = Pts ⟅ o ⟆} (S .F-obᴰ o) e
  can = canonicalize ⊤ S tt*

  canonNat : [nat] → ℕ
  canonNat e = can e .fst .snd .fst

  ⟦-⟧SET : Functor FREECC.C (SET ℓ-zero)
  ⟦-⟧SET = FreeCC.rec ×QUIVER SETCC (mkElimInterpᴰ
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
    module Examples where
      _ : canonNat (((＂ 1 ＂ FREECC.,p [t]) ⋆ₑ FREECC.π₁) ⋆ₑ [su]) ≡ 2
      _ = refl

      _ : Sum.rec (λ _ → true) (λ _ → false)
            (Fib→⊎ (can (([f] FREECC.,p ＂ 0 ＂) ⋆ₑ FREECC.π₁)))
        ≡ false
      _ = refl
