-- Finite multisets well-ordered by size
module Cubical.Categories.Direct.Instances.Bag where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; if_then_else_)
open import Cubical.Data.Nat using (ℕ ; suc ; isSetℕ)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.List.More using (All ; filterL)
open import Cubical.Functions.Logic using (_⊓_ ; ⇔toPath ; ⊤)
import Cubical.HITs.FiniteMultiset as FMS

open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)
open import Cubical.Categories.Direct.Instances.Poset

private
  variable
    ℓ ℓ' : Level

Bag : Type ℓ → Type ℓ
Bag A = FMS.FMSet A

module _ {A : Type ℓ} where
  lengthFM : Bag A → ℕ
  lengthFM = FMS.Rec.f isSetℕ 0 (λ _ n → suc n) (λ _ _ _ → refl)

  fromList : List A → Bag A
  fromList []       = FMS.[]
  fromList (x ∷ xs) = x FMS.∷ fromList xs

  fromList-++ : ∀ as bs → fromList (as ++ bs) ≡ fromList as FMS.++ fromList bs
  fromList-++ []       bs = refl
  fromList-++ (a ∷ as) bs = cong (a FMS.∷_) (fromList-++ as bs)

  lengthFM-fromList : ∀ xs → lengthFM (fromList xs) ≡ length xs
  lengthFM-fromList []       = refl
  lengthFM-fromList (x ∷ xs) = cong suc (lengthFM-fromList xs)

  bagShuffle : ∀ x (L H : Bag A)
    → x FMS.∷ (L FMS.++ H) ≡ L FMS.++ (x FMS.∷ H)
  bagShuffle x L H = FMS.ElimProp.f
    {B = λ L' → x FMS.∷ (L' FMS.++ H) ≡ L' FMS.++ (x FMS.∷ H)}
    (FMS.trunc _ _) refl
    (λ y {L'} IH → FMS.comm x y (L' FMS.++ H) ∙ cong (y FMS.∷_) IH) L

  partitionBag : ∀ p xs
    → fromList xs
    ≡ fromList (filterL p xs) FMS.++ fromList (filterL (λ y → not (p y)) xs)
  partitionBag p []       = refl
  partitionBag p (y ∷ ys) = go (p y)
    where
      go : ∀ b
        → y FMS.∷ fromList ys
        ≡ fromList (if b then y ∷ filterL p ys else filterL p ys)
          FMS.++ fromList (if not b then y ∷ filterL (λ y' → not (p y')) ys
                                    else filterL (λ y' → not (p y')) ys)
      go true  = cong (y FMS.∷_) (partitionBag p ys)
      go false = cong (y FMS.∷_) (partitionBag p ys)
               ∙ bagShuffle y (fromList (filterL p ys))
                              (fromList (filterL (λ y' → not (p y')) ys))

  AllFM : (A → hProp ℓ') → Bag A → hProp ℓ'
  AllFM Q = FMS.Rec.f isSetHProp ⊤ (λ x P → Q x ⊓ P)
    (λ x y P → ⇔toPath (λ (qx , qy , p) → qy , qx , p)
                       (λ (qy , qx , p) → qx , qy , p))

module _ {A : Type} where
  All→AllFM : (Q : A → hProp ℓ-zero) (xs : List A)
    → All (λ z → ⟨ Q z ⟩) xs → ⟨ AllFM Q (fromList xs) ⟩
  All→AllFM Q []       _          = tt*
  All→AllFM Q (x ∷ xs) (qx , qxs) = qx , All→AllFM Q xs qxs

  AllFM→All : (Q : A → hProp ℓ-zero) (xs : List A)
    → ⟨ AllFM Q (fromList xs) ⟩ → All (λ z → ⟨ Q z ⟩) xs
  AllFM→All Q []       _           = tt
  AllFM→All Q (x ∷ xs) (qx , rest) = qx , AllFM→All Q xs rest

module _ (A : Type ℓ) where
  BagWFOrder : WFOrder ℓ ℓ-zero
  BagWFOrder = pullbackWFOrder ℕWFOrder FMS.trunc (lengthFM {A = A})

  BagCat = PosetCat BagWFOrder

  BagDirect : DirectStr {C = BagCat} BagWFOrder
  BagDirect = PosetDirect BagWFOrder
