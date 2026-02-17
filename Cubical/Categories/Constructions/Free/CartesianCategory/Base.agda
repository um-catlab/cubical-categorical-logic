{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.Base where

open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit

open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
-- open import Cubical.Categories.Limits.Terminal.More
-- open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
-- open import Cubical.Categories.Presheaf.More

private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ (Q : ×Quiver ℓQ ℓQ') where
  private module Q = ×Quiver Q
  data Exp : Q.Expr → Q.Expr → Type (ℓ-max ℓQ ℓQ') where
    ↑ₑ_ : ∀ t → Exp (Q.dom t) (Q.cod t)
    idₑ : ∀{Γ} → Exp Γ Γ
    _⋆ₑ_ : ∀{Γ Γ' Γ''}(δ : Exp Γ Γ') → (δ' : Exp Γ' Γ'') →  Exp Γ Γ''
    ⋆ₑIdL : ∀{Γ Δ}(δ : Exp Γ Δ) → idₑ ⋆ₑ δ ≡ δ
    ⋆ₑIdR : ∀{Γ Δ}(δ : Exp Γ Δ) → δ ⋆ₑ idₑ ≡ δ
    ⋆ₑAssoc : ∀{Γ Γ' Γ'' Γ'''}
      (δ : Exp Γ Γ')(δ' : Exp Γ' Γ'')(δ'' : Exp Γ'' Γ''')
      → (δ ⋆ₑ δ') ⋆ₑ δ'' ≡ δ ⋆ₑ (δ' ⋆ₑ δ'')
    isSetExp : ∀{Γ Γ'} → isSet (Exp Γ Γ')
    !ₑ : ∀{Γ} → Exp Γ ⊤
    ⊤η : ∀{Γ}(t : Exp Γ ⊤) → t ≡ !ₑ
    π₁ : ∀{Γ Δ} → Exp (Γ × Δ) Γ
    π₂ : ∀{Γ Δ} → Exp (Γ × Δ) Δ
    ⟨_,_⟩ : ∀{Γ Δ Δ'} → Exp Γ Δ → Exp Γ Δ' → Exp Γ (Δ × Δ')
    ×β₁ : ∀{Γ Δ Δ'}{t : Exp Γ Δ}{t' : Exp Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₁ ≡ t
    ×β₂ : ∀{Γ Δ Δ'}{t : Exp Γ Δ}{t' : Exp Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₂ ≡ t'
    ×η : ∀{Γ Δ Δ'}{t : Exp Γ (Δ × Δ')} → t ≡ ⟨ t ⋆ₑ π₁ , t ⋆ₑ π₂ ⟩

  open Category
  |FreeCartesianCategory| : Category _ _
  |FreeCartesianCategory| .ob = Q.Expr
  |FreeCartesianCategory| .Hom[_,_] = Exp
  |FreeCartesianCategory| .id = idₑ
  |FreeCartesianCategory| ._⋆_ = _⋆ₑ_
  |FreeCartesianCategory| .⋆IdL = ⋆ₑIdL
  |FreeCartesianCategory| .⋆IdR = ⋆ₑIdR
  |FreeCartesianCategory| .⋆Assoc = ⋆ₑAssoc
  |FreeCartesianCategory| .isSetHom = isSetExp

  open CartesianCategory using (C; term; bp)
  open UniversalElement
  FreeCartesianCategory : CartesianCategory _ _
  FreeCartesianCategory .C = |FreeCartesianCategory|
  FreeCartesianCategory .term .vertex = ⊤
  FreeCartesianCategory .term .element = tt
  FreeCartesianCategory .term .universal _ =
    isIsoToIsEquiv ((λ z → !ₑ) , ((λ b → refl) , λ _ → sym $ ⊤η _))
  FreeCartesianCategory .bp (Γ , Δ) .vertex = Γ × Δ
  FreeCartesianCategory .bp (Γ , Δ) .element = π₁ , π₂
  FreeCartesianCategory .bp (Γ , Δ) .universal Θ = isIsoToIsEquiv
    ( (λ z → ⟨ z .fst , z .snd ⟩)
    , (λ _ → ΣPathP (×β₁ , ×β₂))
    , (λ _ → sym $ ×η))
