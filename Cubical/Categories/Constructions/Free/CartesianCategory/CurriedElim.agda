{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.CurriedElim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Limits.CartesianD
open import Cubical.Categories.Displayed.Limits.CartesianV
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Limits
  as CartReindex
open import Cubical.Categories.Displayed.Constructions.Weaken as Wk

open import Cubical.Categories.Constructions.Free.CartesianCategory.Base


private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open CartesianCategory using (C; term; bp)

module _ (Q : ×Quiver ℓQ ℓQ') where
  private
    module Q = ×Quiver Q
  module _
    (CCᴰ : CartesianCategoryᴰ (FreeCartesianCategory Q) ℓCᴰ ℓCᴰ')
    where
    open CartesianCategoryᴰ CCᴰ
    open TerminalᴰNotation _ termᴰ
    open BinProductsᴰNotation bpᴰ
    open UniversalElementᴰ
    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      elim-F-ob : ∀ c → Cᴰ.ob[ c ]
      elim-F-ob (↑ o)     = ı-ob o
      elim-F-ob ⊤         = 𝟙ᴰ
      elim-F-ob (c₁ × c₂) = elim-F-ob c₁ ×ᴰ elim-F-ob c₂

    record Interpᴰ : Type (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-max ℓCᴰ ℓCᴰ')) where
      constructor mkInterpᴰ
      field
        ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]
        ı-hom : ∀ e
          → Cᴰ.Hom[ ↑ₑ e ][ elim-F-ob ı-ob (Q.dom e)
                         , elim-F-ob ı-ob (Q.cod e) ]
    module _ (ı : Interpᴰ)
        where
        open Section
        open Interpᴰ ı
        private
          module R = HomᴰReasoning Cᴰ

        elim-F-hom : ∀ {c c'} (f : |FreeCartesianCategory| Q [ c , c' ]) →
          Cᴰ [ f ][ elim-F-ob ı-ob c , elim-F-ob ı-ob c' ]
        elim-F-hom (↑ₑ t) = ı-hom t
        elim-F-hom idₑ = Cᴰ.idᴰ
        elim-F-hom (f ⋆ₑ g) = elim-F-hom f Cᴰ.⋆ᴰ elim-F-hom g
        elim-F-hom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elim-F-hom f) i
        elim-F-hom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elim-F-hom f) i
        elim-F-hom (⋆ₑAssoc f g h i) =
          Cᴰ.⋆Assocᴰ (elim-F-hom f) (elim-F-hom g) (elim-F-hom h) i
        elim-F-hom (isSetExp f g p q i j) =
          isSetHomᴰ' Cᴰ
          (elim-F-hom f) (elim-F-hom g)
          (cong elim-F-hom p) (cong elim-F-hom q)
          i j
        elim-F-hom !ₑ = !tᴰ _
        elim-F-hom (⊤η f i) =
          (R.rectify {p' = ⊤η f}{fᴰ = elim-F-hom f} $ R.≡out $ 𝟙ueᴰ.ηᴰ) i
        elim-F-hom π₁ = π₁ᴰ
        elim-F-hom π₂ = π₂ᴰ
        elim-F-hom ⟨ f₁ , f₂ ⟩ = elim-F-hom f₁ ,pᴰ elim-F-hom f₂
        elim-F-hom (×β₁ {t = f₁}{t' = f₂} i) =
          (R.rectify {p' = ×β₁} $ R.≡out $ ×βᴰ₁ {f₁ᴰ = elim-F-hom f₁}{f₂ᴰ = elim-F-hom f₂}) i
        elim-F-hom (×β₂ {t = f₁}{t' = f₂} i) =
          (R.rectify {p' = ×β₂} $ R.≡out $ ×βᴰ₂ {f₁ᴰ = elim-F-hom f₁}{f₂ᴰ = elim-F-hom f₂}) i
        elim-F-hom (×η {t = f} i) =
          (R.rectify {p' = ×η {t = f}} $ R.≡out $ ×ueᴰ.ηᴰ _ _ {f = _ , elim-F-hom f}) i

        elim : GlobalSection Cᴰ
        elim .F-obᴰ = elim-F-ob ı-ob
        elim .F-homᴰ = elim-F-hom
        elim .F-idᴰ = refl
        elim .F-seqᴰ _ _ = refl

  module _
    {D : Category ℓD ℓD'}
    {F : Functor (|FreeCartesianCategory| Q) D}
    (Dᴰ : CartesianCategoryⱽ D ℓDᴰ ℓDᴰ') where
    private
      module Dᴰ = CartesianCategoryⱽ Dᴰ
    F*Dᴰ-cartⱽ = CartReindex.reindex F Dᴰ
    F*Dᴰ : CartesianCategoryᴰ (FreeCartesianCategory Q) _ _
    F*Dᴰ = CartesianCategoryⱽ→CartesianCategoryᴰ F*Dᴰ-cartⱽ
    open CartesianCategoryᴰ

    elimLocal : ∀ (ı : Interpᴰ F*Dᴰ) → Section F Dᴰ.Cᴰ
    elimLocal ı = GlobalSectionReindex→Section _ _ (elim F*Dᴰ ı)

  module _ (CC : CartesianCategory ℓC ℓC') where
    private
      wkC = weakenCartesianCategory (FreeCartesianCategory Q) CC
    -- TODO: rec preserves finite products, should follow from
    -- properties of weaken/elim preserved displayed fin products
    rec : (ı : Interpᴰ wkC) → Functor (|FreeCartesianCategory| Q) (CC .C)
    rec ı = introS⁻ (elim wkC ı)
