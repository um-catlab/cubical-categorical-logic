{-# OPTIONS --lossy-unification #-}
module Gluing.Category.BoolNatCanonicity where

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
open import Cubical.Categories.UnderlyingGraph hiding (Interp)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Free.Category.Forded as Free

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Sets

open import Gluing.Canonicity

open Category
open Section
open QuiverOver

module _ where
  data OB : Type where
    ⊤ bool nat : OB

  data MOR : Type ℓ-zero where
    tr fl ze su : MOR

  QUIVER : Quiver ℓ-zero ℓ-zero
  QUIVER .fst = OB
  QUIVER .snd .mor = MOR
  QUIVER .snd .dom tr = ⊤
  QUIVER .snd .dom fl = ⊤
  QUIVER .snd .dom ze = ⊤
  QUIVER .snd .dom su = nat
  QUIVER .snd .cod tr = bool
  QUIVER .snd .cod fl = bool
  QUIVER .snd .cod ze = nat
  QUIVER .snd .cod su = nat

  private
    FQ = FreeCat QUIVER
    module FQ = Category FQ

  [bool] : Type _
  [bool] = FQ [ ⊤ , bool ]

  [t] [f] : [bool]
  [t] = ⇑ QUIVER tr
  [f] = ⇑ QUIVER fl

  [nat] : Type _
  [nat] = FQ [ ⊤ , nat ]

  [ze] : [nat]
  [ze] = ⇑ QUIVER ze

  [su] : FQ [ nat , nat ]
  [su] = ⇑ QUIVER su

  ＂_＂ : ℕ → [nat]
  ＂ zero ＂ = [ze]
  ＂ suc n ＂ = ＂ n ＂ ⋆⟨ FQ ⟩ [su]

  CanonicalFormBool : [bool] → hSet ℓ-zero
  CanonicalFormBool e =
    ((e ≡ [t]) ⊎ (e ≡ [f])) ,
    isSet⊎ (isProp→isSet (FQ.isSetHom _ _))
           (isProp→isSet (FQ.isSetHom _ _))

  CanonicalFormNat : [nat] → hSet ℓ-zero
  CanonicalFormNat e =
    fiber ＂_＂ e ,
    isSetΣ isSetℕ (λ _ → isProp→isSet (FQ.isSetHom _ _))

  private
    Pts : Functor FQ (SET ℓ-zero)
    Pts = FQ [ ⊤ ,-]

    ıo : ∀ o → FQ [ ⊤ , o ] → hSet ℓ-zero
    ıo ⊤ e = (e ≡ FQ.id) , (isProp→isSet (FQ.isSetHom _ _))
    ıo bool e = CanonicalFormBool e
    ıo nat e = CanonicalFormNat e

    ıe : ∀ (m : MOR) (e : Exp QUIVER ⊤ (QUIVER .snd .dom m)) →
      ⟨ ıo (QUIVER .snd .dom m) e ⟩ →
      ⟨ ıo (QUIVER .snd .cod m) (e ⋆⟨ FQ ⟩ ⇑ QUIVER m) ⟩
    ıe tr e e≡id = inl (cong (FQ ∘ [t]) e≡id ∙ FQ.⋆IdL _)
    ıe fl e e≡id = inr (cong (FQ ∘ [f]) e≡id ∙ FQ.⋆IdL _)
    ıe ze e e≡id = 0 , sym (cong (FQ ∘ [ze]) e≡id ∙ FQ.⋆IdL _)
    ıe su e (n , fib) = suc n , cong (FQ ∘ [su]) fib

    ıh : ∀ (m : MOR) → Pointwise ℓ-zero {X = Pts ⟅ QUIVER .snd .dom m ⟆}
      {Y = Pts ⟅ QUIVER .snd .cod m ⟆} (Pts ⟪ ⇑ QUIVER m ⟫)
      (ıo (QUIVER .snd .dom m)) (ıo (QUIVER .snd .cod m))
    ıh m z = (z .fst ⋆⟨ FQ ⟩ ⇑ QUIVER m , ıe m (z .fst) (z .snd)) , refl

  S : Section Pts (SETCod ℓ-zero)
  S = Free.elimLocal QUIVER _ _ (record
    { _$gᴰ_ = ıo
    ; _<$g>ᴰ_ = λ m → mk ℓ-zero {X = Pts ⟅ QUIVER .snd .dom m ⟆}
        {Y = Pts ⟅ QUIVER .snd .cod m ⟆} {h = Pts ⟪ ⇑ QUIVER m ⟫}
        {P = ıo (QUIVER .snd .dom m)} {Q = ıo (QUIVER .snd .cod m)}
        (ıh m) })

  can : ∀ {o} (e : FQ [ ⊤ , o ]) → Fib ℓ-zero {Y = Pts ⟅ o ⟆} (ıo o) e
  can = canonicalize ⊤ S refl

  canonNat : [nat] → ℕ
  canonNat e = can e .fst .snd .fst

  ⟦-⟧SET : Functor FQ (SET ℓ-zero)
  ⟦-⟧SET = Free.rec QUIVER (record
    { _$g_ = λ { ⊤ → Unit , isSetUnit
                ; bool → Bool , isSetBool
                ; nat → ℕ , isSetℕ }
    ; _<$g>_ = λ { tr → λ _ → true ; fl → λ _ → false
                  ; ze → λ _ → 0 ; su → suc } })

  evalBool : [bool] → Bool
  evalBool e = ⟦-⟧SET .Functor.F-hom e tt

  evalNat : [nat] → ℕ
  evalNat e = ⟦-⟧SET .Functor.F-hom e tt

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
      _ : canonNat ((FQ.id ⋆⟨ FQ ⟩ ＂ 2 ＂) ⋆⟨ FQ ⟩ (FQ.id ⋆⟨ FQ ⟩ [su])) ≡ 3
      _ = refl

      _ : Sum.rec (λ _ → true) (λ _ → false) (Fib→⊎ (can (FQ.id ⋆⟨ FQ ⟩ [f])))
        ≡ false
      _ = refl
