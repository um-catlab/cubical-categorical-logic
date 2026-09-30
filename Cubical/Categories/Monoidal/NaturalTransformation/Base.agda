module Cubical.Categories.Monoidal.NaturalTransformation.Base where
open import Cubical.Foundations.Prelude

open import Cubical.Categories.NaturalTransformation
private
  variable
    ℓM ℓM' ℓN ℓN' : Level

open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.Base hiding (MonoidalStr)

module _ (M : MonoidalCategory ℓM ℓM') (N : MonoidalCategory ℓN ℓN') where
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N

  module _ (F G : LaxMonoidalFunctor M N) where

    module _ (φ : NatTrans (F .LaxMonoidalFunctor.F) (G .LaxMonoidalFunctor.F)) where
      record MonoidalStr : Type (ℓ-max ℓN' ℓM)
        where
        private
          module F = LaxMonoidalFunctor F
          module G = LaxMonoidalFunctor G

        field
          μ-law : ∀ (x y : M.ob) →
            φ ⟦ x ⟧ N.⊗ₕ φ ⟦ y ⟧ N.⋆ G.μ⟨ x , y ⟩ ≡
            (F.μ⟨ x , y ⟩ N.⋆ φ ⟦ x M.⊗ y ⟧)
          ε-law : F.ε N.⋆ (φ ⟦ M.unit ⟧) ≡ G.ε

    record MonoidalNatTrans : Type (ℓ-max (ℓ-max ℓM' ℓM) ℓN') where
      field
        φ : NatTrans (F .LaxMonoidalFunctor.F) (G .LaxMonoidalFunctor.F)
        monstr : MonoidalStr φ
      open NatTrans φ public
      open MonoidalStr monstr public
