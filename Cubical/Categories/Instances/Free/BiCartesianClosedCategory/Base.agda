{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.BiCartesianClosed.Base

open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver

private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ (Q : +×⇒Quiver ℓQ ℓQ') where
  private module Q = +×⇒Quiver Q

  data Expr : Q.obExpr → Q.obExpr → Type (ℓ-max ℓQ ℓQ') where
    -- Freely added Category structure
    ↑ₑ_ : ∀ t → Expr (Q.dom t) (Q.cod t)
    idₑ : ∀{Γ} → Expr Γ Γ
    _⋆ₑ_ : ∀{Γ Γ' Γ''}(δ : Expr Γ Γ') → (δ' : Expr Γ' Γ'') →  Expr Γ Γ''
    ⋆ₑIdL : ∀{Γ Δ}(δ : Expr Γ Δ) → idₑ ⋆ₑ δ ≡ δ
    ⋆ₑIdR : ∀{Γ Δ}(δ : Expr Γ Δ) → δ ⋆ₑ idₑ ≡ δ
    ⋆ₑAssoc : ∀{Γ Γ' Γ'' Γ'''}
      (δ : Expr Γ Γ')(δ' : Expr Γ' Γ'')(δ'' : Expr Γ'' Γ''')
      → (δ ⋆ₑ δ') ⋆ₑ δ'' ≡ δ ⋆ₑ (δ' ⋆ₑ δ'')
    isSetExpr : ∀{Γ Γ'} → isSet (Expr Γ Γ')
    -- Freely added Terminal structure
    !ₑ : ∀{Γ} → Expr Γ ⊤
    ⊤η : ∀{Γ}(t : Expr Γ ⊤) → t ≡ !ₑ
    -- Freely added Initial structure
    absurd : ∀{B} → Expr ⊥ B
    ⊥η : ∀{B}(t : Expr ⊥ B) → t ≡ absurd
    -- Freely added BinProducts structure
    π₁ : ∀{Γ Δ} → Expr (Γ × Δ) Γ
    π₂ : ∀{Γ Δ} → Expr (Γ × Δ) Δ
    ⟨_,_⟩ : ∀{Γ Δ Δ'} → Expr Γ Δ → Expr Γ Δ' → Expr Γ (Δ × Δ')
    ×β₁ : ∀{Γ Δ Δ'}{t : Expr Γ Δ}{t' : Expr Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₁ ≡ t
    ×β₂ : ∀{Γ Δ Δ'}{t : Expr Γ Δ}{t' : Expr Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₂ ≡ t'
    ×η : ∀{Γ Δ Δ'}{t : Expr Γ (Δ × Δ')} → t ≡ ⟨ t ⋆ₑ π₁ , t ⋆ₑ π₂ ⟩
    -- Freely added BinCoProducts structure
    σ₁ : ∀{Γ Δ} → Expr Γ (Γ + Δ)
    σ₂ : ∀{Γ Δ} → Expr Δ (Γ + Δ)
    [_,_] : ∀{Γ Δ Δ'} → Expr Δ Γ → Expr Δ' Γ → Expr (Δ + Δ') Γ
    +β₁ : ∀{Γ Δ Δ'}{t : Expr Δ Γ}{t' : Expr Δ' Γ} → σ₁ ⋆ₑ [ t , t' ] ≡ t
    +β₂ : ∀{Γ Δ Δ'}{t : Expr Δ Γ}{t' : Expr Δ' Γ} → σ₂ ⋆ₑ [ t , t' ] ≡ t'
    +η : ∀{Γ Δ Δ'}{t : Expr (Δ + Δ') Γ} → t ≡ [ σ₁ ⋆ₑ t , σ₂ ⋆ₑ t ]
    -- Freely added Exponentials structure
    eval : ∀{Δ Θ} → Expr ((Δ ⇒ Θ) × Δ) Θ
    λ-_ : ∀{Γ Δ Θ} → Expr (Γ × Δ) Θ → Expr Γ (Δ ⇒ Θ)
    λβ : ∀{Γ Δ Θ} → (t : Expr (Γ × Δ) Θ) → (⟨ π₁ ⋆ₑ (λ- t) , π₂ ⟩ ⋆ₑ eval) ≡ t
    λη : ∀{Γ Δ Θ} → (t : Expr Γ (Δ ⇒ Θ)) → t ≡ (λ- (⟨ π₁ ⋆ₑ t , π₂ ⟩ ⋆ₑ eval))

  open Category hiding (_∘_)
  open CartesianCategory using (C; term; bp)
  open CartesianClosedCategory using (CC; exps)
  open BiCartesianClosedCategory using (CCC; sums; init)
  open UniversalElement

  FreeBiCartesianClosedCategory : BiCartesianClosedCategory _ _
  FreeBiCartesianClosedCategory .CCC .CC .C .ob = Q.obExpr
  FreeBiCartesianClosedCategory .CCC .CC .C .Hom[_,_] = Expr
  FreeBiCartesianClosedCategory .CCC .CC .C .id = idₑ
  FreeBiCartesianClosedCategory .CCC .CC .C ._⋆_ = _⋆ₑ_
  FreeBiCartesianClosedCategory .CCC .CC .C .⋆IdL = ⋆ₑIdL
  FreeBiCartesianClosedCategory .CCC .CC .C .⋆IdR = ⋆ₑIdR
  FreeBiCartesianClosedCategory .CCC .CC .C .⋆Assoc = ⋆ₑAssoc
  FreeBiCartesianClosedCategory .CCC .CC .C .isSetHom = isSetExpr
  FreeBiCartesianClosedCategory .CCC .CC .term .vertex = ⊤
  FreeBiCartesianClosedCategory .CCC .CC .term .element = tt
  FreeBiCartesianClosedCategory .CCC .CC .term .universal _ =
    isIsoToIsEquiv ((λ z → !ₑ) , ((λ b → refl) , λ _ → sym $ ⊤η _))
  FreeBiCartesianClosedCategory .CCC .CC .bp (Γ , Δ) .vertex = Γ × Δ
  FreeBiCartesianClosedCategory .CCC .CC .bp (Γ , Δ) .element = π₁ , π₂
  FreeBiCartesianClosedCategory .CCC .CC .bp (Γ , Δ) .universal Θ = isIsoToIsEquiv
    ( (λ z → ⟨ z .fst , z .snd ⟩)
    , (λ _ → ΣPathP (×β₁ , ×β₂))
    , (λ _ → sym $ ×η))
  FreeBiCartesianClosedCategory .CCC .exps Δ Θ .vertex = Δ ⇒ Θ
  FreeBiCartesianClosedCategory .CCC .exps Δ Θ .element = eval
  FreeBiCartesianClosedCategory .CCC .exps Δ Θ .universal Γ = isIsoToIsEquiv
    (λ-_ , λβ , sym ∘ λη)
  FreeBiCartesianClosedCategory .sums (Γ , Δ) .vertex = Γ + Δ
  FreeBiCartesianClosedCategory .sums (Γ , Δ) .element = σ₁ , σ₂
  FreeBiCartesianClosedCategory .sums (Γ , Δ) .universal Θ = isIsoToIsEquiv
    ( (λ z → [ z .fst , z .snd ])
    , (λ _ → ΣPathP (+β₁ , +β₂))
    , (λ _ → sym $ +η))
  FreeBiCartesianClosedCategory .init .vertex = ⊥
  FreeBiCartesianClosedCategory .init .element = tt
  FreeBiCartesianClosedCategory .init .universal _ =
    isIsoToIsEquiv ((λ z → absurd) , ((λ b → refl) , λ _ → sym $ ⊥η _))
