{- Various large associator combinators etc -}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal.Base
module Cubical.Categories.Monoidal.Combinators.Equations
  where

open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.NaturalTransformation.More hiding (α)
open import Cubical.Categories.Monoidal.Functor
import Cubical.Categories.Monoidal.Combinators.Base as Combinators
open import Cubical.Categories.Constructions.Free.Monoidal.Base
open import Cubical.Categories.Constructions.Free.Monoidal.Coherence
open import Cubical.Data.SumFin

open Category
open Functor
private
  α4⁻¹α-lhs : ∀ {ℓ ℓ' : Level} (M : MonoidalCategory ℓ ℓ') →
    ∀ x x' x'' x''' x'''' x'''''
    → (MonoidalCategory.C M) [ _ , _ ]
  α4⁻¹α-lhs M x x' x'' x''' x'''' x''''' =
    MComb.α4⁻¹⟨ x , x' , x'' , x''' , x'''' ⟩ M.⊗ₕ M.id {x'''''}
    M.∘ M.α⟨ x M.⊗ (x' M.⊗ (x'' M.⊗ x''')) , x'''' , x''''' ⟩
    where module M = MonoidalCategory M
          module MComb = Combinators M
  α4⁻¹α-rhs : ∀ {ℓ ℓ' : Level} (M : MonoidalCategory ℓ ℓ') →
    ∀ x x' x'' x''' x'''' x'''''
    → (MonoidalCategory.C M) [ _ , _ ]
  α4⁻¹α-rhs M x x' x'' x''' x'''' x''''' =
    MComb.α4⟨ x , x' , x'' , x''' M.⊗ x'''' , x''''' ⟩
    M.∘ (M.id M.⊗ₕ (M.id M.⊗ₕ (M.id M.⊗ₕ M.α⟨ x''' , x'''' , x''''' ⟩)))
    M.∘ MComb.α4⁻¹⟨ x , x' , x'' , x''' , x'''' M.⊗ x''''' ⟩
    where module M = MonoidalCategory M
          module MComb = Combinators M

  ηα-lhs ηα-rhs : ∀ {ℓ ℓ' : Level} (M : MonoidalCategory ℓ ℓ') →
    ∀ x x'
    → (MonoidalCategory.C M) [ _ , _ ]
  ηα-lhs M x x' = (M.η⟨ x ⟩ M.⊗ₕ M.id {x'}) M.∘ M.α⟨ M.unit , x , x' ⟩
    where module M = MonoidalCategory M
  ηα-rhs M x x' = M.η⟨ x M.⊗ x' ⟩
    where module M = MonoidalCategory M

private
  F6 = FreeMonoidalCategory (Fin 6)
  module F6 = MonoidalCategory F6

  x x' x'' x''' x'''' x''''' : F6.ob
  x = ↑ (fromℕ 0)
  x' = ↑ (fromℕ 1)
  x'' = ↑ (fromℕ 2)
  x''' = ↑ (fromℕ 3)
  x'''' = ↑ (fromℕ 4)
  x''''' = ↑ (fromℕ 5)
  α4⁻¹α-free :
    α4⁻¹α-lhs F6 x x' x'' x''' x'''' x'''''
    ≡ α4⁻¹α-rhs F6 x x' x'' x''' x'''' x'''''
  α4⁻¹α-free = coherence (Fin 6 , isSetFin) _ _

α4⁻¹α :
  ∀ {ℓ ℓ' : Level} (M : MonoidalCategory ℓ ℓ')
  → ∀ x x' x'' x''' x'''' x'''''
  → α4⁻¹α-lhs M x x' x'' x''' x'''' x'''''
  ≡ α4⁻¹α-rhs M x x' x'' x''' x'''' x'''''
α4⁻¹α M x x' x'' x''' x'''' x''''' = cong (sem.F .F-hom) α4⁻¹α-free
  where
    module M = MonoidalCategory M
    ı : Fin 6 → M.ob
    ı (inl _) = x
    ı (fsuc (inl x₁)) = x'
    ı (fsuc (fsuc (inl x₁))) = x''
    ı (fsuc (fsuc (fsuc (inl x₁)))) = x'''
    ı (fsuc (fsuc (fsuc (fsuc (inl x₁))))) = x''''
    ı (fsuc (fsuc (fsuc (fsuc (fsuc (inl x₁)))))) = x'''''
    sem = rec (Fin 6) M ı
    module sem = StrongMonoidalFunctor sem

private
  F2 = FreeMonoidalCategory (Fin 2)
  module F2 = MonoidalCategory F2

  y y' : F2.ob
  y = ↑ (fromℕ 0)
  y' = ↑ (fromℕ 1)
  ηα-free : ηα-lhs F2 y y' ≡ ηα-rhs F2 y y'
  ηα-free = coherence (Fin 2 , isSetFin) _ _

ηα : ∀ {ℓ ℓ'} (M : MonoidalCategory ℓ ℓ')
  → ∀ x x'
  → ηα-lhs M x x' ≡ ηα-rhs M x x'
ηα M x x' = cong (sem.F .F-hom) ηα-free
  where
    module M = MonoidalCategory M
    ı : Fin 2 → M.ob
    ı (inl x₁) = x
    ı (fsuc x₁) = x'
    sem = rec (Fin 2) M ı
    module sem = StrongMonoidalFunctor sem
