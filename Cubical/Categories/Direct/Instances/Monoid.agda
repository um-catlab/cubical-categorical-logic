module Cubical.Categories.Direct.Instances.Monoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm ; +-assoc)
open import Cubical.Data.Nat.Order.Recursive using (_≤_ ; n≤k+n)
import Cubical.Data.Equality as Eq
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.Instances.Nat using (NatMonoid)

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Elements
open import Cubical.Categories.Functor
open import Cubical.Data.Sigma
open import Cubical.Categories.Instances.Delooping
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)

open Functor

GradedMonoid : Type₁
GradedMonoid = Σ[ M ∈ Monoid ℓ-zero ] MonoidHom M NatMonoid

split≤ : ∀ a b c → a + b ≡ c → WFOrder._≤_ ℕWFOrder b c
split≤ zero    b c p = inr (Eq.pathToEq p)
split≤ (suc a) b c p = inl (subst (suc b ≤_) p (n≤k+n {k = a} b))

_^opGM : GradedMonoid → GradedMonoid
((M , deg , isHom) ^opGM) .fst .fst = ⟨ M ⟩
((M , deg , isHom) ^opGM) .fst .snd = monoidstr ε (λ x y → y · x)
  (makeIsMonoid is-set (λ x y z → sym (·Assoc z y x)) ·IdL ·IdR)
  where open MonoidStr (M .snd)
((M , deg , isHom) ^opGM) .snd .fst = deg
((M , deg , isHom) ^opGM) .snd .snd .IsMonoidHom.presε = IsMonoidHom.presε isHom
((M , deg , isHom) ^opGM) .snd .snd .IsMonoidHom.pres· x y =
  IsMonoidHom.pres· isHom y x ∙ +-comm (deg y) (deg x)

module _ ((M , deg , isHom) : GradedMonoid) where
  open MonoidStr (M .snd)
  open IsMonoidHom isHom

  Suffix : Category ℓ-zero ℓ-zero
  Suffix = Covariant.∫_ {C = B M ^op} (B M [-, tt ])

  BothSides : Monoid ℓ-zero
  BothSides .fst = ⟨ M ⟩ × ⟨ M ⟩
  BothSides .snd = monoidstr (ε , ε) (λ (h , k) (h' , k') → h' · h , k · k')
    (makeIsMonoid (isSet× is-set is-set)
      (λ (h , k) (h' , k') (h'' , k'') → ΣPathP (sym (·Assoc h'' h' h) , ·Assoc k k' k''))
      (λ (h , k) → ΣPathP (·IdL h , ·IdR k))
      (λ (h , k) → ΣPathP (·IdR h , ·IdL k)))

  twoSided : Functor (B BothSides) (SET ℓ-zero)
  twoSided .F-ob _ = M .fst , is-set
  twoSided .F-hom (h , k) u = h · u · k
  twoSided .F-id = funExt λ u → cong (_· ε) (·IdL u) ∙ ·IdR u
  twoSided .F-seq (h , k) (h' , k') = funExt λ u →
      ·Assoc (h' · h · u) k k'
    ∙ cong (λ z → z · k · k') (sym (·Assoc h' h u))
    ∙ cong (_· k') (sym (·Assoc h' (h · u) k))

  Factor : Category ℓ-zero ℓ-zero
  Factor = Covariant.∫_ {C = B BothSides} twoSided

  suffixDirect : DirectStr Suffix ℕWFOrder
  suffixDirect = mkDirectStr Suffix ℕWFOrder (λ (_ , u) → deg u)
    λ {(_ , u)} {(_ , w)} (h , p) → split≤ (deg h) (deg u) (deg w) (sym (pres· h u) ∙ cong deg p)

  factorDirect : DirectStr Factor ℕWFOrder
  factorDirect = mkDirectStr Factor ℕWFOrder (λ (_ , u) → deg u)
    λ {(_ , u)} {(_ , w)} ((h , k) , p) →
      split≤ (deg h + deg k) (deg u) (deg w)
        ( sym (+-assoc (deg h) (deg k) (deg u))
        ∙ cong (deg h +_) (+-comm (deg k) (deg u))
        ∙ +-assoc (deg h) (deg u) (deg k)
        ∙ cong (_+ deg k) (sym (pres· h u))
        ∙ sym (pres· (h · u) k)
        ∙ cong deg p)

module _ (GM : GradedMonoid) where
  Prefix : Category ℓ-zero ℓ-zero
  Prefix = Suffix (GM ^opGM)

  prefixDirect : DirectStr Prefix ℕWFOrder
  prefixDirect = suffixDirect (GM ^opGM)
