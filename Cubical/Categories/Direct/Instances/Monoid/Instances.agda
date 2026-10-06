module Cubical.Categories.Direct.Instances.Monoid.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; inj-+m ; isSetℕ ; +-zero ; +-suc ; snotz)
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Order.Recursive using (_<_ ; _≤_ ; isProp≤ ; n≤k+n)
import Cubical.Data.Nat.Order.Recursive as NatOrd
import Cubical.Data.Equality as Eq
open import Cubical.Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; rev)
open import Cubical.Data.List.Properties using (length++ ; rev-++ ; rev-rev ; cons-inj₂)
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.Instances.Nat using (NatMonoid)
open import Cubical.Algebra.Monoid.Instances.List using (ListMonoid)
open import Cubical.HITs.FiniteMultiset as FMS using (FMSet)
open import Cubical.HITs.FiniteMultiset.Properties using (unitl-++ ; unitr-++ ; assoc-++)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Foundations.Isomorphism using (isoToIsEquiv ; iso)
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)
open import Cubical.Categories.Direct.Instances.Monoid

open Functor

ℕGM : GradedMonoid
ℕGM = NatMonoid , (λ n → n) , monoidequiv refl λ _ _ → refl

StringGM : hSet ℓ-zero → GradedMonoid
StringGM Σ = ListMonoid Σ , length , monoidequiv refl length++

module _ (A : hSet ℓ-zero) where
  sizeFM : FMSet ⟨ A ⟩ → ℕ
  sizeFM = FMS.Rec.f isSetℕ 0 (λ _ n → suc n) (λ _ _ _ → refl)

  sizeFM-++ : ∀ xs ys → sizeFM (xs FMS.++ ys) ≡ sizeFM xs + sizeFM ys
  sizeFM-++ xs ys = FMS.ElimProp.f {B = λ xs → sizeFM (xs FMS.++ ys) ≡ sizeFM xs + sizeFM ys}
    (isSetℕ _ _) refl (λ _ p → cong suc p) xs

  BagGM : GradedMonoid
  BagGM .fst .fst = FMSet ⟨ A ⟩
  BagGM .fst .snd = monoidstr FMS.[] FMS._++_ (makeIsMonoid FMS.trunc assoc-++ unitr-++ unitl-++)
  BagGM .snd = sizeFM , monoidequiv refl sizeFM-++

module _ ((M , deg , isHom) : GradedMonoid) where
  open MonoidStr (M .snd)

  isRightCancellative : Type
  isRightCancellative = ∀ x y u → x · u ≡ y · u → x ≡ y

  isThinSuffix : isRightCancellative → ∀ u w → isProp (Suffix (M , deg , isHom) [ (tt , u) , (tt , w) ])
  isThinSuffix canc u w (h , p) (h' , p') = Σ≡Prop (λ _ → is-set _ _) (canc h h' u (p ∙ sym p'))

ℕ-cancel : isRightCancellative ℕGM
ℕ-cancel x y u = inj-+m

module _ {Σ : Type} where
  ++-cancelˡ : ∀ (u x y : List Σ) → u ++ x ≡ u ++ y → x ≡ y
  ++-cancelˡ []      x y p = p
  ++-cancelˡ (c ∷ u) x y p = ++-cancelˡ u x y (cons-inj₂ p)

  ++-cancelʳ : ∀ (x y u : List Σ) → x ++ u ≡ y ++ u → x ≡ y
  ++-cancelʳ x y u p =
    sym (rev-rev x)
    ∙ cong rev (++-cancelˡ (rev u) (rev x) (rev y) (sym (rev-++ x u) ∙ cong rev p ∙ rev-++ y u))
    ∙ rev-rev y

String-cancel : ∀ Σ → isRightCancellative (StringGM Σ)
String-cancel Σ = ++-cancelʳ

private
  ≤→Σ : ∀ m n → m ≤ n → Σ[ h ∈ ℕ ] h + m ≡ n
  ≤→Σ zero    n       _ = n , +-zero n
  ≤→Σ (suc m) zero    ()
  ≤→Σ (suc m) (suc n) p = let (h , e) = ≤→Σ m n p in h , +-suc h m ∙ cong suc e

ω : Category ℓ-zero ℓ-zero
ω = WFOrder→Cat ℕWFOrder

ω→Suffix : Functor ω (Suffix ℕGM)
ω→Suffix .F-ob n = tt , n
ω→Suffix .F-hom {m} {n} (inl q) =
  let (h , e) = ≤→Σ (suc m) n q in suc h , sym (+-suc h m) ∙ e
ω→Suffix .F-hom {m} (inr Eq.refl) = 0 , refl
ω→Suffix .F-id = isThinSuffix ℕGM ℕ-cancel _ _ _ _
ω→Suffix .F-seq _ _ = isThinSuffix ℕGM ℕ-cancel _ _ _ _

ω→Suffix-FF : isFullyFaithful ω→Suffix
ω→Suffix-FF m n = isoToIsEquiv (iso _ (λ (h , p) → split≤ h m n p)
  (λ _ → isThinSuffix ℕGM ℕ-cancel _ _ _ _)
  (λ _ → WFOrder.isProp≤ ℕWFOrder _ _))

ℕ-conical : ∀ (x : ℕ) → x ≡ 0 → x ≡ 0
ℕ-conical x p = p

String-conical : (Alph : hSet ℓ-zero) (x : List ⟨ Alph ⟩) → length x ≡ 0 → x ≡ []
String-conical Alph []      _ = refl
String-conical Alph (c ∷ x) p = ⊥.rec (snotz p)
