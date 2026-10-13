{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Instances.Free.CartesianCategory.UncurriedElim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit

open import
  Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Weaken.Base
open import Cubical.Categories.Displayed.Instances.Weaken.UncurriedProperties

open import Cubical.Categories.Instances.Free.CartesianCategory.Base
open import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver

private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Section
open PshHom
open PshIso

module _ (Q : ×Quiver ℓQ ℓQ') where
  private module Q = ×Quiver Q
  module _
    (CCᴰ : CartesianCategoryᴰ (FreeCartesianCategory Q) ℓCᴰ ℓCᴰ')
    where
    open CartesianCategoryᴰ CCᴰ
    open UniversalElementᴰNotation
    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      elimOb : ∀ A → Cᴰ.ob[ A ]
      elimOb (↑ o) = ı-ob o
      elimOb (A × B) = bpᴰ (elimOb A) (elimOb B) .fst
      elimOb ⊤ = termᴰ .fst

    record Interpᴰ : Type (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-max ℓCᴰ ℓCᴰ')) where
      constructor mkInterpᴰ
      field
        ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]
        ı-hom : ∀ e
          → Cᴰ.Hom[ ↑ₑ e ][ elimOb ı-ob (Q.dom e) , elimOb ı-ob (Q.cod e) ]

    module _ (ı : Interpᴰ) where
      open Interpᴰ ı
      elimHom : ∀ {A A'} (f : |FreeCartesianCategory| Q [ A , A' ]) →
        Cᴰ [ f ][ elimOb ı-ob A , elimOb ı-ob A' ]
      elimHom (↑ₑ t) = ı-hom t
      elimHom idₑ = Cᴰ.idᴰ
      elimHom (f ⋆ₑ g) = elimHom f Cᴰ.⋆ᴰ elimHom g
      elimHom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elimHom f) i
      elimHom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elimHom f) i
      elimHom (⋆ₑAssoc f g h i) = Cᴰ.⋆Assocᴰ (elimHom f) (elimHom g) (elimHom h) i
      elimHom (isSetExp f g p q i j) =
        isSetHomᴰ' Cᴰ (elimHom f) (elimHom g) (λ i → elimHom (p i)) (λ i → elimHom (q i)) i j
      elimHom !ₑ = termᴰ.introᴰ tt
      elimHom (⊤η f i) = Cᴰ.rectify {e' = ⊤η f} (termᴰ.ηᴰ (elimHom f)) i
      elimHom (π₁ {A}{B}) = bpᴰ.πᴰ₁
      elimHom (π₂ {A}{B}) = bpᴰ.πᴰ₂
      elimHom ⟨ f , g ⟩ = bpᴰ.introᴰ ((elimHom f) , (elimHom g))
      -- these rectifies are I think because universalElement is based on equiv not iso
      elimHom (×β₁ {Γ}{A}{B}{f}{g} i) = Cᴰ.rectify {e' = ×β₁} (bpᴰ.×βᴰ₁ (elimHom f) (elimHom g)) i
      elimHom (×β₂ {Γ}{A}{B}{f}{g} i) = Cᴰ.rectify {e' = ×β₂} (bpᴰ.×βᴰ₂ (elimHom f) (elimHom g)) i
      elimHom (×η {Γ}{A}{B}{f} i) = Cᴰ.rectify {e' = ×η} (bpᴰ.×ηᴰ (elimHom f)) i

      elim : GlobalSection Cᴰ
      elim .F-obᴰ = elimOb ı-ob
      elim .F-homᴰ = elimHom
      elim .F-idᴰ = refl
      elim .F-seqᴰ = λ _ _ → refl

      -- TODO: show this is actually a "cartesian closed" section

  module _
    {D : Category ℓD ℓD'}
    (F : Functor (|FreeCartesianCategory| Q) D)
    (CCⱽ : CartesianCategoryⱽ D ℓCᴰ ℓCᴰ')
    where
    open CartesianCategoryⱽ CCⱽ

    elimLocalMotive : CartesianCategoryᴰ (FreeCartesianCategory Q) ℓCᴰ ℓCᴰ'
    elimLocalMotive = CartesianCategoryⱽ→CartesianCategoryᴰ (FreeCartesianCategory Q)
      (CartesianCategoryⱽReindex CCⱽ F)

    elimLocal : (ı : Interpᴰ elimLocalMotive) → Section F Cᴰ
    elimLocal ı = GlobalSectionReindex→Section Cᴰ F (elim elimLocalMotive ı)

  module _ (CC : CartesianCategory ℓC ℓC') where
    private
      wkC = weakenCartesianCategory (FreeCartesianCategory Q) CC
    -- TODO: rec preserves finite products, should follow from
    -- properties of weaken/elim preserved displayed fin products
    rec : (ı : Interpᴰ wkC) → Functor (|FreeCartesianCategory| Q) (CC .CartesianCategory.C)
    rec ı = introS⁻ (elim wkC ı)
