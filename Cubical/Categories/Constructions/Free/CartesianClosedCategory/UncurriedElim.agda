{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Constructions.Free.CartesianClosedCategory.UncurriedElim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Quiver hiding (Expr)
open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Base

open import Cubical.Categories.Displayed.Base
-- open import Cubical.Categories.Displayed.Limits.BinProduct.Base
-- open import Cubical.Categories.Displayed.Limits.Terminal
-- open import Cubical.Categories.Displayed.Limits.CartesianD
open import Cubical.Categories.Displayed.Limits.CartesianClosedD
-- open import Cubical.Categories.Displayed.Exponentials.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Section


private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Section

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  private module Q = ×⇒QuiverNotation Q

  module _ (CCCᴰ : CartesianClosedCategoryᴰ (FreeCartesianClosedCategory Q) ℓCᴰ ℓCᴰ') where
    open CartesianClosedCategoryᴰ CCCᴰ

    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      elimOb : ∀ A → Cᴰ.ob[ A ]
      elimOb (↑ o) = ı-ob o
      elimOb ⊤ = termᴰ .fst
      elimOb (A × B) = bpᴰ (elimOb A) (elimOb B) .fst
      elimOb (A ⇒ B) = expᴰ (elimOb A) (elimOb B) .fst

    record Interpᴰ : Type (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-max ℓCᴰ ℓCᴰ')) where
      field
        ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]
        ı-hom : ∀ e → Cᴰ.Hom[ ↑ₑ e ][ elimOb ı-ob (Q.Dom e) , elimOb ı-ob (Q.Cod e) ]

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
      elimHom (⊤η f i) = Cᴰ.rectify {p' = ⊤η f} (termᴰ.ηᴰ (elimHom f)) i
      elimHom (π₁ {A}{B}) = bpᴰ.πᴰ₁
      elimHom (π₂ {A}{B}) = bpᴰ.πᴰ₂
      elimHom ⟨ f , g ⟩ = bpᴰ.introᴰ ((elimHom f) , (elimHom g))
      elimHom (×β₁ {Γ}{A}{B}{f}{g} i) = Cᴰ.rectify {p' = ×β₁} (bpᴰ.×βᴰ₁ (elimHom f) (elimHom g)) i
      elimHom (×β₂ {Γ}{A}{B}{f}{g} i) = Cᴰ.rectify {p' = ×β₂} (bpᴰ.×βᴰ₂ (elimHom f) (elimHom g)) i
      elimHom (×η {Γ}{A}{B}{f} i) = Cᴰ.rectify {p' = ×η} (bpᴰ.×ηᴰ (elimHom f)) i
      elimHom eval = appᴰ
      elimHom (λ- e) = λᴰ (elimHom e)
      elimHom (λβ e i) = Cᴰ.rectify {p' = λβ e} (Cᴰ.≡out $ ⇒βᴰ (elimHom e)) i
      elimHom (λη e i) = Cᴰ.rectify {p' = λη e} (Cᴰ.≡out $ ⇒ηᴰ (elimHom e)) i

      elim : GlobalSection Cᴰ
      elim .F-obᴰ = elimOb ı-ob
      elim .F-homᴰ = elimHom
      elim .F-idᴰ = refl
      elim .F-seqᴰ = λ _ _ → refl

  -- module _
  --
  --   where
  --   open CartesianCategoryᴰ (CCCᴰ .fst)
  --   open TerminalᴰNotation _ termᴰ
  --   open BinProductsᴰNotation bpᴰ
  --   open ExponentialsᴰNotation _ (CCCᴰ .snd)

  --   module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
  --     elim-F-ob : ∀ c → Cᴰ.ob[ c ]
  --     elim-F-ob (↑ o) = ı-ob o
  --     elim-F-ob (Γ × Δ) = elim-F-ob Γ ×ᴰ elim-F-ob Δ
  --     elim-F-ob ⊤ = 𝟙ᴰ
  --     elim-F-ob (c ⇒ c') = elim-F-ob c ⇒ᴰ elim-F-ob c'


  --   module _ (ı : Interpᴰ) where
  --     open Section
  --     open Interpᴰ ı
  --     private
  --       module R = HomᴰReasoning Cᴰ

  --     elim-F-hom : ∀ {c c'} (f : FreeCartesianClosedCategory .CC .C [ c , c' ]) →
  --       Cᴰ.Hom[ f ][ elim-F-ob ı-ob c , elim-F-ob ı-ob c' ]
  --     -- elim-F-hom for CartesianCategory structure
  --     elim-F-hom (↑ₑ t) = ı-hom t
  --     elim-F-hom idₑ = Cᴰ.idᴰ
  --     elim-F-hom (f ⋆ₑ g) = elim-F-hom f Cᴰ.⋆ᴰ elim-F-hom g
  --     elim-F-hom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elim-F-hom f) i
  --     elim-F-hom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elim-F-hom f) i
  --     elim-F-hom (⋆ₑAssoc f g h i) = Cᴰ.⋆Assocᴰ (elim-F-hom f) (elim-F-hom g) (elim-F-hom h) i
  --     elim-F-hom (isSetExpr f g p q i j) = isSetHomᴰ' (Cᴰ)
  --       (elim-F-hom f) (elim-F-hom g)
  --       (cong elim-F-hom p) (cong elim-F-hom q)
  --       i j
  --     elim-F-hom !ₑ = !tᴰ _
  --     elim-F-hom (⊤η f i) = R.rectify {p' = ⊤η f} {fᴰ = elim-F-hom f} (R.≡out (𝟙ueᴰ.ηᴰ)) i
  --     elim-F-hom π₁ = π₁ᴰ
  --     elim-F-hom π₂ = π₂ᴰ
  --     elim-F-hom ⟨ f , g ⟩ = elim-F-hom f ,pᴰ elim-F-hom g
  --     elim-F-hom (×β₁ {t = f} {t' = g} i) = R.rectify {p' = ×β₁}
  --       (R.≡out (×βᴰ₁ {f₁ᴰ = elim-F-hom f} {f₂ᴰ = elim-F-hom g})) i
  --     elim-F-hom (×β₂ {t = f} {t' = g} i) = R.rectify {p' = ×β₂}
  --       (R.≡out (×βᴰ₂ {f₁ᴰ = elim-F-hom f} {f₂ᴰ = elim-F-hom g})) i
  --     elim-F-hom (×η {t = f} i) = R.rectify {p' = ×η {t = f}} (R.≡out (×ueᴰ.ηᴰ _ _ {f = _ , elim-F-hom f})) i
  --     -- elim-F-hom for Exponentials structure
  --     elim-F-hom eval = appᴰ {cᴰ = elim-F-ob ı-ob _} {c'ᴰ = elim-F-ob ı-ob _}
  --     elim-F-hom (λ- f) = ldaᴰ (elim-F-hom f)
  --     elim-F-hom (λβ f i) = R.rectify {p' = λβ f} (R.≡out (βᴰ {fᴰ = elim-F-hom f})) i
  --     elim-F-hom (λη f i) = R.rectify {p' = λη f} (R.≡out (ηᴰ {fᴰ = elim-F-hom f})) i

  --     elim : GlobalSection (Cᴰ)
  --     elim .F-obᴰ = elim-F-ob ı-ob
  --     elim .F-homᴰ = elim-F-hom
  --     elim .F-idᴰ = refl
  --     elim .F-seqᴰ _ _ = refl
