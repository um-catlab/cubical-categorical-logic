{-# OPTIONS --lossy-unification #-}
module Gluing.BiCartesianClosedCategory.BoolNatCanonicity.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum.Properties
open import Cubical.Data.Unit
open import Cubical.Data.Quiver.Base
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Displayed.Constructions.Weaken.UncurriedProperties
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Constructions.Free.BiCartesianClosedCategory.Forded as FreeBiCCC
  renaming ([_,_] to [_,+_])
open import Cubical.Categories.Constructions.Free.BiCartesianClosedCategory.Quiver

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
    S : Section (FREEBICCC.C [ ⊤ ,-]) (SETᴰ ℓ-zero ℓ-zero)
    S = FreeBiCCC.elimLocal +×⇒QUIVER
      (CorepCartesian FREEBICCC.CC ⊤)
      EqSETᴰBCCCⱽ (mkElimInterpᴰ
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
    (λ e → canonicalize ⊤ S _ e)

  canonicity-nat : Iso [nat] ℕ
  canonicity-nat = NatIso.canonicity-nat ＂_＂ evalNat evalNat-＂_＂
    (λ e → canonicalize ⊤ S _ e)
