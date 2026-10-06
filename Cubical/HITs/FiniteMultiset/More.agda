module Cubical.HITs.FiniteMultiset.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.List.More using (All ; Ilv)
open import Cubical.Functions.Logic using (_⊓_ ; ⇔toPath ; ⊤)
open import Cubical.HITs.FiniteMultiset as FMS using (FMSet)

private
  variable
    ℓ ℓ' : Level

module _ {A : Type ℓ} where
  fromList : List A → FMSet A
  fromList []       = FMS.[]
  fromList (x ∷ xs) = x FMS.∷ fromList xs

  fromList-++ : ∀ as bs → fromList (as ++ bs) ≡ fromList as FMS.++ fromList bs
  fromList-++ []       bs = refl
  fromList-++ (a ∷ as) bs = cong (a FMS.∷_) (fromList-++ as bs)

  bagShuffle : ∀ x (L H : FMSet A)
    → x FMS.∷ (L FMS.++ H) ≡ L FMS.++ (x FMS.∷ H)
  bagShuffle x L H = FMS.ElimProp.f
    {B = λ L' → x FMS.∷ (L' FMS.++ H) ≡ L' FMS.++ (x FMS.∷ H)}
    (FMS.trunc _ _) refl
    (λ y {L'} IH → FMS.comm x y (L' FMS.++ H) ∙ cong (y FMS.∷_) IH) L

  Ilv→fromList : ∀ {u v} w → Ilv u v w → fromList w ≡ fromList u FMS.++ fromList v
  Ilv→fromList [] (p , q) = cong₂ (λ a b → fromList a FMS.++ fromList b) (sym p) (sym q)
  Ilv→fromList (x ∷ w) (inl (u' , p , i)) =
    cong (x FMS.∷_) (Ilv→fromList w i) ∙ cong (λ a → fromList a FMS.++ _) (sym p)
  Ilv→fromList {u} (x ∷ w) (inr (v' , p , i)) =
    cong (x FMS.∷_) (Ilv→fromList w i) ∙ bagShuffle x (fromList u) (fromList v')
    ∙ cong (λ b → fromList u FMS.++ fromList b) (sym p)

  AllFM : (A → hProp ℓ') → FMSet A → hProp ℓ'
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
