{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Instances.Free.CartesianClosedCategory.UncurriedElim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.CartesianClosed
open import Cubical.Categories.Displayed.Instances.Weaken.Base
open import Cubical.Categories.Displayed.Instances.Weaken.UncurriedProperties


private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

open Section

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  private
    module Q = ×⇒Quiver Q
    module FreeCCC = CartesianClosedCategory (FreeCartesianClosedCategory Q)

  module _ (CCCᴰ : CartesianClosedCategoryᴰ (FreeCartesianClosedCategory Q) ℓCᴰ ℓCᴰ') where
    open CartesianClosedCategoryᴰ CCCᴰ

    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      elimOb : ∀ A → Cᴰ.ob[ A ]
      elimOb (↑ o) = ı-ob o
      elimOb ⊤ = termᴰ .fst
      elimOb (A × B) = bpᴰ (elimOb A) (elimOb B) .fst
      elimOb (A ⇒ B) = expᴰ (elimOb A) (elimOb B) .fst

    record Interpᴰ : Type (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-max ℓCᴰ ℓCᴰ')) where
      constructor interpᴰ
      field
        ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]
        ı-hom : ∀ e → Cᴰ.Hom[ ↑ₑ e ][ elimOb ı-ob (Q.dom e) , elimOb ı-ob (Q.cod e) ]

    module _ (ı : Interpᴰ) where
      open Interpᴰ ı

      elimHom : ∀ {A B} (e : Expr Q A B)
        → Cᴰ.Hom[ e ][ elimOb ı-ob A , elimOb ı-ob B ]
      elimHom (↑ₑ t) = ı-hom t
      elimHom idₑ = Cᴰ.idᴰ
      elimHom (e ⋆ₑ e') = elimHom e Cᴰ.⋆ᴰ elimHom e'
      elimHom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elimHom f) i
      elimHom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elimHom f) i
      elimHom (⋆ₑAssoc f g h i) = Cᴰ.⋆Assocᴰ (elimHom f) (elimHom g) (elimHom h) i
      elimHom (isSetExpr f g p q i j) =
        isSetHomᴰ' Cᴰ (elimHom f) (elimHom g) (λ i → elimHom (p i)) (λ i → elimHom (q i)) i j
      elimHom !ₑ = termᴰ.introᴰ tt
      elimHom (⊤η f i) = Cᴰ.rectify {e' = ⊤η f} (termᴰ.ηᴰ (elimHom f)) i
      elimHom (π₁ {A}{B}) = bpᴰ.πᴰ₁
      elimHom (π₂ {A}{B}) = bpᴰ.πᴰ₂
      elimHom ⟨ f , g ⟩ = bpᴰ.introᴰ ((elimHom f) , (elimHom g))
      elimHom (×β₁ {Γ}{A}{B}{f}{g} i) = Cᴰ.rectify {e' = ×β₁} (bpᴰ.×βᴰ₁ (elimHom f) (elimHom g)) i
      elimHom (×β₂ {Γ}{A}{B}{f}{g} i) = Cᴰ.rectify {e' = ×β₂} (bpᴰ.×βᴰ₂ (elimHom f) (elimHom g)) i
      elimHom (×η {Γ}{A}{B}{f} i) = Cᴰ.rectify {e' = ×η} (bpᴰ.×ηᴰ (elimHom f)) i
      elimHom eval = appᴰ
      elimHom (λ- e) = λᴰ (elimHom e)
      elimHom (λβ e i) = Cᴰ.rectify {e' = λβ e} (Cᴰ.≡out $ ⇒βᴰ (elimHom e)) i
      elimHom (λη e i) = Cᴰ.rectify {e' = λη e} (Cᴰ.≡out $ ⇒ηᴰ (elimHom e)) i

      elim : GlobalSection Cᴰ
      elim .F-obᴰ = elimOb ı-ob
      elim .F-homᴰ = elimHom
      elim .F-idᴰ = refl
      elim .F-seqᴰ = λ _ _ → refl

  module _
    {D : CartesianCategory ℓD ℓD'}
    (F : CartesianFunctor
      (FreeCartesianClosedCategory Q .CartesianClosedCategory.CC)
      (D .CartesianCategory.C))
    (CCCⱽ : CartesianClosedCategoryⱽ D ℓCᴰ ℓCᴰ')
    where
    elimLocalMotive : CartesianClosedCategoryᴰ (FreeCartesianClosedCategory Q) _ _
    elimLocalMotive = CartesianClosedCategoryⱽ→CartesianClosedCategoryᴰ
      (FreeCartesianClosedCategory Q)
      (CCCⱽReindex CCCⱽ F)

    elimLocal : (ı : Interpᴰ elimLocalMotive) → Section (F .fst) (CCCⱽ .CartesianClosedCategoryⱽ.Cᴰ)
    elimLocal ı = GlobalSectionReindex→Section _ _ (elim elimLocalMotive ı)
  module _ (CCC : CartesianClosedCategory ℓC ℓC') where
    private
      wkC = weakenCCC (FreeCartesianClosedCategory Q) CCC
      module CCC = CartesianClosedCategory CCC
    rec : (ı : Interpᴰ wkC) → Functor FreeCCC.C CCC.C
    rec ı = introS⁻ (elim wkC ı)
