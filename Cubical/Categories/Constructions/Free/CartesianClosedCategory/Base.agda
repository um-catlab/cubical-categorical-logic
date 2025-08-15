--{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Constructions.Free.CartesianClosedCategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Quiver hiding (Expr)

private
  variable
    ℓQ ℓQ' ℓC ℓC' : Level

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  private module Q = ×⇒QuiverNotation Q

  data Expr : Q.Ob → Q.Ob → Type (ℓ-max ℓQ ℓQ') where
    -- c/p from Free/CartesianCategory
    -- Did we always just c/p this, or is there a better way excepting things like macros
    -- BEGIN COPY
    ↑ₑ_ : ∀ t → Expr (Q.Dom t) (Q.Cod t)
    idₑ : ∀{Γ} → Expr Γ Γ
    _⋆ₑ_ : ∀{Γ Γ' Γ''}(δ : Expr Γ Γ') → (δ' : Expr Γ' Γ'') →  Expr Γ Γ''
    ⋆ₑIdL : ∀{Γ Δ}(δ : Expr Γ Δ) → idₑ ⋆ₑ δ ≡ δ
    ⋆ₑIdR : ∀{Γ Δ}(δ : Expr Γ Δ) → δ ⋆ₑ idₑ ≡ δ
    ⋆ₑAssoc : ∀{Γ Γ' Γ'' Γ'''}
      (δ : Expr Γ Γ')(δ' : Expr Γ' Γ'')(δ'' : Expr Γ'' Γ''')
      → (δ ⋆ₑ δ') ⋆ₑ δ'' ≡ δ ⋆ₑ (δ' ⋆ₑ δ'')
    isSetExpr : ∀{Γ Γ'} → isSet (Expr Γ Γ')
    !ₑ : ∀{Γ} → Expr Γ ⊤
    ⊤η : ∀{Γ}(t : Expr Γ ⊤) → t ≡ !ₑ
    π₁ : ∀{Γ Δ} → Expr (Γ × Δ) Γ
    π₂ : ∀{Γ Δ} → Expr (Γ × Δ) Δ
    ⟨_,_⟩ : ∀{Γ Δ Δ'} → Expr Γ Δ → Expr Γ Δ' → Expr Γ (Δ × Δ')
    ×β₁ : ∀{Γ Δ Δ'}{t : Expr Γ Δ}{t' : Expr Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₁ ≡ t
    ×β₂ : ∀{Γ Δ Δ'}{t : Expr Γ Δ}{t' : Expr Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₂ ≡ t'
    ×η : ∀{Γ Δ Δ'}{t : Expr Γ (Δ × Δ')} → t ≡ ⟨ t ⋆ₑ π₁ , t ⋆ₑ π₂ ⟩
    -- END COPY
    -- Exponential stuff
    eval : ∀{Δ Θ} → Expr ((Δ ⇒ Θ) × Δ) Θ
    λ-_ : ∀{Γ Δ Θ} → Expr (Γ × Δ) Θ → Expr Γ (Δ ⇒ Θ)
    λβ : ∀{Γ Δ Θ} → (t : Expr (Γ × Δ) Θ) → (⟨ π₁ ⋆ₑ (λ- t) , π₂ ⟩ ⋆ₑ eval) ≡ t
    λη : ∀{Γ Δ Θ} → (t : Expr Γ (Δ ⇒ Θ)) → (λ- (⟨ π₁ ⋆ₑ t , π₂ ⟩ ⋆ₑ eval)) ≡ t


  open Category
  open CartesianCategory
  open CartesianClosedCategory
  open UniversalElement

  -- this is also largely copied from Free/CartesianCategory
  -- is there a good way to avoid that...?
  FreeCartesianClosedCategory : CartesianClosedCategory _ _
  -- BEGIN COPY
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
  -- END COPY
  FreeCartesianClosedCategory .exps Δ Θ .vertex = Δ ⇒ Θ
  FreeCartesianClosedCategory .exps Δ Θ .element = eval
  FreeCartesianClosedCategory .exps Δ Θ .universal Γ = isIsoToIsEquiv
    (λ-_ ,
    λβ ,
    λη)
