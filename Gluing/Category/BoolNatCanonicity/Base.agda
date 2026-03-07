module Gluing.Category.BoolNatCanonicity.Base where

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

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Free.Category.Quiver as Free

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base

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
  [t] = ↑ tr
  [f] = ↑ fl

  [nat] : Type _
  [nat] = FQ [ ⊤ , nat ]

  [ze] : [nat]
  [ze] = ↑ ze

  [su] : FQ [ nat , nat ]
  [su] = ↑ su

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
      ⟨ ıo (QUIVER .snd .cod m) (e ⋆⟨ FQ ⟩ (↑ m)) ⟩
    ıe tr e e≡id = inl (cong (FQ ∘ [t]) e≡id ∙ FQ.⋆IdL _)
    ıe fl e e≡id = inr (cong (FQ ∘ [f]) e≡id ∙ FQ.⋆IdL _)
    ıe ze e e≡id = 0 , sym (cong (FQ ∘ [ze]) e≡id ∙ FQ.⋆IdL _)
    ıe su e (n , fib) = suc n , cong (FQ ∘ [su]) fib

    S : Section Pts (SETᴰ _ _)
    S = Free.elimLocal QUIVER _ _ (record
      { _$gᴰ_ = ıo
      ; _<$g>ᴰ_ = ıe })

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
  canonicity-bool .Iso.fun = evalBool
  canonicity-bool .Iso.inv = λ { true → [t] ; false → [f] }
  canonicity-bool .Iso.sec = λ { true → refl ; false → refl }
  canonicity-bool .Iso.ret e =
    Sum.elim {C = λ _ → canonicity-bool .Iso.inv (evalBool e) ≡ e}
      (λ p → cong (λ x → canonicity-bool .Iso.inv (evalBool x)) p ∙ sym p)
      (λ q → cong (λ x → canonicity-bool .Iso.inv (evalBool x)) q ∙ sym q)
      (canonicalize ⊤ S refl e)

  canonicity-nat : Iso [nat] ℕ
  canonicity-nat .Iso.fun = evalNat
  canonicity-nat .Iso.inv n = ＂ n ＂
  canonicity-nat .Iso.sec n = evalNat-＂ n ＂
  canonicity-nat .Iso.ret [n] =
    cong ＂_＂ (cong evalNat (sym p) ∙ evalNat-＂ m ＂) ∙ p
    where
    m = canonicalize ⊤ S refl [n] .fst
    p = canonicalize ⊤ S refl [n] .snd
