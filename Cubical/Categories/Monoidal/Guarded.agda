module Cubical.Categories.Monoidal.Guarded where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.NaturalTransformation.Base

open Functor

private
  variable
    ℓV ℓV' : Level

module _ {V : MonoidalCategory ℓV ℓV'} where
  private
    module V = MonoidalCategory V

  module _ (▷Lax : LaxMonoidalFunctor V V) (next : MonoidalNatTrans V V IdLax ▷Lax) where
    private
      ▷F : V.ob → V.ob
      ▷F = ▷Lax .LaxMonoidalFunctor.F .F-ob

      next⟦_⟧ : ∀ X → V.Hom[ X , ▷F X ]
      next⟦ X ⟧ = next .MonoidalNatTrans.N-ob X

    record GuardedStr : Type (ℓ-max ℓV ℓV') where
      field
        fix : ∀ {X} → V.Hom[ ▷F X , X ] → V.Hom[ V.unit , X ]
        fix-fix : ∀ {X} (f : V.Hom[ ▷F X , X ])
          → fix f ≡ (fix f V.⋆ next⟦ X ⟧) V.⋆ f
        fix-uniq : ∀ {X} (f : V.Hom[ ▷F X , X ]) (u : V.Hom[ V.unit , X ])
          → u ≡ (u V.⋆ next⟦ X ⟧) V.⋆ f → u ≡ fix f

module _ (V : MonoidalCategory ℓV ℓV') where
  private
    module V = MonoidalCategory V

  record GuardedModel : Type (ℓ-max ℓV ℓV') where
    field
      ▷Lax : LaxMonoidalFunctor V V
      next : MonoidalNatTrans V V IdLax ▷Lax
      guardedStr : GuardedStr ▷Lax next
    open GuardedStr guardedStr public

    ▷F : V.ob → V.ob
    ▷F = ▷Lax .LaxMonoidalFunctor.F .F-ob

    next⟦_⟧ : ∀ X → V.Hom[ X , ▷F X ]
    next⟦ X ⟧ = next .MonoidalNatTrans.N-ob X
