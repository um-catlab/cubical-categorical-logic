{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianClosedCategory.BoolNatCanonicity.UncurriedElim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure hiding (⟨_⟩)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties

open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Quiver as FreeCCC
open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Base as FreeCCC
open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.UncurriedElim as FreeCCC

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

  ×⇒QUIVER : ×⇒Quiver ℓ-zero ℓ-zero
  ×⇒QUIVER .×⇒Quiver.ob = OB
  ×⇒QUIVER .×⇒Quiver.Q .mor = MOR
  ×⇒QUIVER .×⇒Quiver.Q .dom tr = ⊤
  ×⇒QUIVER .×⇒Quiver.Q .dom fl = ⊤
  ×⇒QUIVER .×⇒Quiver.Q .dom ze = ⊤
  ×⇒QUIVER .×⇒Quiver.Q .dom su = ↑ nat
  ×⇒QUIVER .×⇒Quiver.Q .cod tr = ↑ bool
  ×⇒QUIVER .×⇒Quiver.Q .cod fl = ↑ bool
  ×⇒QUIVER .×⇒Quiver.Q .cod ze = ↑ nat
  ×⇒QUIVER .×⇒Quiver.Q .cod su = ↑ nat

  private
    FREECCC = FreeCartesianClosedCategory ×⇒QUIVER
    module FREECCC = CartesianClosedCategory FREECCC

  [bool] : Type _
  [bool] = FREECCC.Hom[ ⊤ , ↑ bool ]

  [t] [f] : [bool]
  [t] = ↑ₑ tr
  [f] = ↑ₑ fl

  [nat] : Type _
  [nat] = FREECCC.Hom[ ⊤ , ↑ nat ]

  [ze] : [nat]
  [ze] = ↑ₑ ze

  [su] : FREECCC.Hom[ ↑ nat , ↑ nat ]
  [su] = ↑ₑ su

  ＂_＂ : ℕ → [nat]
  ＂ zero ＂ = [ze]
  ＂ suc n ＂ = ＂ n ＂ ⋆ₑ [su]

  CanonicalFormBool : [bool] → hSet ℓ-zero
  CanonicalFormBool e =
    ((e ≡ [t]) ⊎ (e ≡ [f])) ,
    isSet⊎ (isProp→isSet (FREECCC.isSetHom _ _))
           (isProp→isSet (FREECCC.isSetHom _ _))

  CanonicalFormNat : [nat] → hSet ℓ-zero
  CanonicalFormNat e =
    fiber ＂_＂ e ,
    isSetΣ isSetℕ (λ _ → isProp→isSet (FREECCC.isSetHom _ _))

  private
    S : Section (FREECCC.C [ ⊤ ,-]) (SETᴰ ℓ-zero ℓ-zero)
    S = FreeCCC.elimLocal ×⇒QUIVER
      (CorepCartesian FREECCC.CC ⊤)
      EqSETᴰCCCⱽ (interpᴰ
      (λ { bool e → CanonicalFormBool e ; nat e → CanonicalFormNat e })
      λ { tr e _ → inl (cong₂ _⋆ₑ_ (⊤→⊤IsId FREECCC.term e) refl
                        ∙ FREECCC.⋆IdL _)
        ; fl e _ → inr (cong₂ _⋆ₑ_ (⊤→⊤IsId FREECCC.term e) refl
                        ∙ FREECCC.⋆IdL _)
        ; ze e _ → 0 , (sym (cong₂ _⋆ₑ_ (⊤→⊤IsId FREECCC.term e) refl
                             ∙ FREECCC.⋆IdL _))
        ; su e (n , fib) → (suc n) , cong₂ _⋆ₑ_ fib refl
        })

  ⟦-⟧SET : Functor FREECCC.C (SET ℓ-zero)
  ⟦-⟧SET = FreeCCC.rec ×⇒QUIVER SETCCC (interpᴰ
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
