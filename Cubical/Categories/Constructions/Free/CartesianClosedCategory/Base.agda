{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Constructions.Free.CartesianClosedCategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Quiver hiding (Expr)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Exponentials.CartesianClosed
open import Cubical.Categories.Displayed.Exponentials.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Section
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  private module Q = ×⇒QuiverNotation Q

  data Expr : Q.Ob → Q.Ob → Type (ℓ-max ℓQ ℓQ') where
    -- Freely added Category structure
    ↑ₑ_ : ∀ t → Expr (Q.Dom t) (Q.Cod t)
    idₑ : ∀{Γ} → Expr Γ Γ
    _⋆ₑ_ : ∀{Γ Γ' Γ''}(δ : Expr Γ Γ') → (δ' : Expr Γ' Γ'') →  Expr Γ Γ''
    ⋆ₑIdL : ∀{Γ Δ}(δ : Expr Γ Δ) → idₑ ⋆ₑ δ ≡ δ
    ⋆ₑIdR : ∀{Γ Δ}(δ : Expr Γ Δ) → δ ⋆ₑ idₑ ≡ δ
    ⋆ₑAssoc : ∀{Γ Γ' Γ'' Γ'''}
      (δ : Expr Γ Γ')(δ' : Expr Γ' Γ'')(δ'' : Expr Γ'' Γ''')
      → (δ ⋆ₑ δ') ⋆ₑ δ'' ≡ δ ⋆ₑ (δ' ⋆ₑ δ'')
    isSetExpr : ∀{Γ Γ'} → isSet (Expr Γ Γ')
    -- Freely added BinProducts structure
    !ₑ : ∀{Γ} → Expr Γ ⊤
    ⊤η : ∀{Γ}(t : Expr Γ ⊤) → t ≡ !ₑ
    π₁ : ∀{Γ Δ} → Expr (Γ × Δ) Γ
    π₂ : ∀{Γ Δ} → Expr (Γ × Δ) Δ
    ⟨_,_⟩ : ∀{Γ Δ Δ'} → Expr Γ Δ → Expr Γ Δ' → Expr Γ (Δ × Δ')
    ×β₁ : ∀{Γ Δ Δ'}{t : Expr Γ Δ}{t' : Expr Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₁ ≡ t
    ×β₂ : ∀{Γ Δ Δ'}{t : Expr Γ Δ}{t' : Expr Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₂ ≡ t'
    ×η : ∀{Γ Δ Δ'}{t : Expr Γ (Δ × Δ')} → t ≡ ⟨ t ⋆ₑ π₁ , t ⋆ₑ π₂ ⟩
    -- Freely added Exponentials structure
    eval : ∀{Δ Θ} → Expr ((Δ ⇒ Θ) × Δ) Θ
    λ-_ : ∀{Γ Δ Θ} → Expr (Γ × Δ) Θ → Expr Γ (Δ ⇒ Θ)
    λβ : ∀{Γ Δ Θ} → (t : Expr (Γ × Δ) Θ) → (⟨ π₁ ⋆ₑ (λ- t) , π₂ ⟩ ⋆ₑ eval) ≡ t
    λη : ∀{Γ Δ Θ} → (t : Expr Γ (Δ ⇒ Θ)) → t ≡ (λ- (⟨ π₁ ⋆ₑ t , π₂ ⟩ ⋆ₑ eval))

  open Category hiding (_∘_)
  open CartesianCategory
  open CartesianClosedCategory
  open UniversalElement

  FreeCartesianClosedCategory : CartesianClosedCategory _ _
  -- The CartesianCategory structure is copied from Free/CartesianCategory
  FreeCartesianClosedCategory .CC .C .ob = Q.Ob
  FreeCartesianClosedCategory .CC .C .Hom[_,_] = Expr
  FreeCartesianClosedCategory .CC .C .id = idₑ
  FreeCartesianClosedCategory .CC .C ._⋆_ = _⋆ₑ_
  FreeCartesianClosedCategory .CC .C .⋆IdL = ⋆ₑIdL
  FreeCartesianClosedCategory .CC .C .⋆IdR = ⋆ₑIdR
  FreeCartesianClosedCategory .CC .C .⋆Assoc = ⋆ₑAssoc
  FreeCartesianClosedCategory .CC .C .isSetHom = isSetExpr
  FreeCartesianClosedCategory .CC .term .vertex = ⊤
  FreeCartesianClosedCategory .CC .term .element = tt
  FreeCartesianClosedCategory .CC .term .universal _ =
    isIsoToIsEquiv ((λ z → !ₑ) , ((λ b → refl) , λ _ → sym $ ⊤η _))
  FreeCartesianClosedCategory .CC .bp (Γ , Δ) .vertex = Γ × Δ
  FreeCartesianClosedCategory .CC .bp (Γ , Δ) .element = π₁ , π₂
  FreeCartesianClosedCategory .CC .bp (Γ , Δ) .universal Θ = isIsoToIsEquiv
    ( (λ z → ⟨ z .fst , z .snd ⟩)
    , (λ _ → ΣPathP (×β₁ , ×β₂))
    , (λ _ → sym $ ×η))
  -- The Exponentials structure
  FreeCartesianClosedCategory .exps Δ Θ .vertex = Δ ⇒ Θ
  FreeCartesianClosedCategory .exps Δ Θ .element = eval
  FreeCartesianClosedCategory .exps Δ Θ .universal Γ = isIsoToIsEquiv
    (λ-_ , λβ , sym ∘ λη)

  module _
    (CCCᴰ : CartesianClosedCategoryᴰ FreeCartesianClosedCategory ℓCᴰ ℓCᴰ')
    where
    open CartesianCategoryᴰ (CCCᴰ .fst)
    open TerminalᴰNotation _ termᴰ
    open BinProductsᴰNotation bpᴰ
    open ExponentialsᴰNotation _ (CCCᴰ .snd)

    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      elim-F-ob : ∀ c → Cᴰ.ob[ c ]
      elim-F-ob (↑ o) = ı-ob o
      elim-F-ob (Γ × Δ) = elim-F-ob Γ ×ᴰ elim-F-ob Δ
      elim-F-ob ⊤ = 𝟙ᴰ
      elim-F-ob (c ⇒ c') = elim-F-ob c ⇒ᴰ elim-F-ob c'

    record Interpᴰ : Type (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-max ℓCᴰ ℓCᴰ')) where
      field
        ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]
        ı-hom : ∀ e → Cᴰ.Hom[ ↑ₑ e ][ elim-F-ob ı-ob (Q.Dom e) , elim-F-ob ı-ob (Q.Cod e) ]

    module _ (ı : Interpᴰ) where
      open Section
      open Interpᴰ ı
      private
        module R = HomᴰReasoning Cᴰ

      elim-F-hom : ∀ {c c'} (f : FreeCartesianClosedCategory .CC .C [ c , c' ]) →
        Cᴰ.Hom[ f ][ elim-F-ob ı-ob c , elim-F-ob ı-ob c' ]
      -- elim-F-hom for CartesianCategory structure
      elim-F-hom (↑ₑ t) = ı-hom t
      elim-F-hom idₑ = Cᴰ.idᴰ
      elim-F-hom (f ⋆ₑ g) = elim-F-hom f Cᴰ.⋆ᴰ elim-F-hom g
      elim-F-hom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elim-F-hom f) i
      elim-F-hom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elim-F-hom f) i
      elim-F-hom (⋆ₑAssoc f g h i) = Cᴰ.⋆Assocᴰ (elim-F-hom f) (elim-F-hom g) (elim-F-hom h) i
      elim-F-hom (isSetExpr f g p q i j) = isSetHomᴰ' (Cᴰ)
        (elim-F-hom f) (elim-F-hom g)
        (cong elim-F-hom p) (cong elim-F-hom q)
        i j
      elim-F-hom !ₑ = !tᴰ _
      elim-F-hom (⊤η f i) = R.rectify {p' = ⊤η f} {fᴰ = elim-F-hom f} (R.≡out (𝟙ueᴰ.ηᴰ)) i
      elim-F-hom π₁ = π₁ᴰ
      elim-F-hom π₂ = π₂ᴰ
      elim-F-hom ⟨ f , g ⟩ = elim-F-hom f ,pᴰ elim-F-hom g
      elim-F-hom (×β₁ {t = f} {t' = g} i) = R.rectify {p' = ×β₁}
        (R.≡out (×βᴰ₁ {f₁ᴰ = elim-F-hom f} {f₂ᴰ = elim-F-hom g})) i
      elim-F-hom (×β₂ {t = f} {t' = g} i) = R.rectify {p' = ×β₂}
        (R.≡out (×βᴰ₂ {f₁ᴰ = elim-F-hom f} {f₂ᴰ = elim-F-hom g})) i
      elim-F-hom (×η {t = f} i) = R.rectify {p' = ×η {t = f}} (R.≡out (×ueᴰ.ηᴰ _ _ {f = _ , elim-F-hom f})) i
      -- elim-F-hom for Exponentials structure
      elim-F-hom eval = appᴰ {cᴰ = elim-F-ob ı-ob _} {c'ᴰ = elim-F-ob ı-ob _}
      elim-F-hom (λ- f) = ldaᴰ (elim-F-hom f)
      elim-F-hom (λβ f i) = R.rectify {p' = λβ f} (R.≡out (βᴰ {fᴰ = elim-F-hom f})) i
      elim-F-hom (λη f i) = R.rectify {p' = λη f} (R.≡out (ηᴰ {fᴰ = elim-F-hom f})) i

      elim : GlobalSection (Cᴰ)
      elim .F-obᴰ = elim-F-ob ı-ob
      elim .F-homᴰ = elim-F-hom
      elim .F-idᴰ = refl
      elim .F-seqᴰ _ _ = refl
