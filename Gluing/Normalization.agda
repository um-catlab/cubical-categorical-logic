module Gluing.Normalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.HITs.GroupoidTruncation
open import Cubical.HITs.SetTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
  hiding (_×_)
open import Cubical.Categories.Constructions.Free.CartesianCategory.Base
  hiding (rec)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Base

private variable
  ℓq ℓq' : Level

open Category
open Functor

module _ (Q : ×Quiver ℓq ℓq') where
  Cl : CartesianCategory _ _
  Cl = FreeCartesianCategory Q
  private
    module CC = CartesianCategoryNotation Cl
    module Prod = Notation _ (Cl .snd .snd)
  data NeutralTerm : (τ : Cl .fst .ob) (Γ : Cl .fst .ob) → Type (ℓ-max ℓq ℓq') where
    var : ∀{τ : Cl .fst .ob} → NeutralTerm τ τ
    proj₁ : ∀{τ₁ τ₂ : Cl .fst .ob} → NeutralTerm τ₁ (τ₁ Prod.× τ₂)
    proj₂ : ∀{τ₁ τ₂ : Cl .fst .ob} → NeutralTerm τ₂ (τ₁ Prod.× τ₂)
    isSetNe : ∀{τ Γ} → isSet (NeutralTerm τ Γ)
  data NormalForm : (τ : Cl .fst .ob) (Γ : Cl .fst .ob) → Type (ℓ-max ℓq ℓq') where
    shift : ∀{τ Γ} → NeutralTerm τ Γ → NormalForm τ Γ
    pair : ∀{τ₁ τ₂ Γ} → NormalForm τ₁ Γ → NormalForm τ₂ Γ → NormalForm (τ₁ Prod.× τ₂) Γ
    isSetNf : ∀{τ Γ} → isSet (NormalForm τ Γ)
  --Ren : Category _ _
  --Ren = DiscreteCategory (∥ Cl .fst .ob ∥₃ , isGroupoidGroupoidTrunc)
  --Ren' : Category _ _
  --Ren' .ob = Cl .fst .ob
  --Ren' .Hom[_,_] Γ Δ = ∥ Γ ≡ Δ ∥₂
  --Ren' .id = ∣ refl ∣₂ --refl
  --Ren' ._⋆_ = rec2 isSetSetTrunc λ p q → ∣ p ∙ q ∣₂ --_∙_
  --Ren' .⋆IdL ∣ r ∣₂ = congS ∣_∣₂ (sym (lUnit _)) --sym (lUnit _)
  --Ren' .⋆IdL (squash₂ r s a b i j) = cong₄ {!!} {!!} {!!} {!!} {!!} --sym (lUnit _)
  --Ren' .⋆IdR _ = {!!} --sym (rUnit _)
  --Ren' .⋆Assoc _ _ _ = {!!} --sym (assoc _ _ _)
  --Ren' .isSetHom = isSetSetTrunc
  --data Disc : (Γ : Cl .fst .ob) (Δ : Cl .fst .ob) → Type ℓq where
  --  self : ∀ Γ  → Disc Γ Γ
  --module _ (Γ : Cl .fst .ob) where
  --  discreteDisc : Discrete (Disc Γ Γ)
  --  discreteDisc = sectionDiscrete {A = ℕ} (λ _ → self Γ) (λ _ → 0) (λ _ → {!!}) discreteℕ
  --isSetDisc : ∀{Γ Δ} → isSet (Disc Γ Δ)
  --isSetDisc = Discrete→isSet {!!}
  --Ren'' : Category _ _
  --Ren'' .ob = Cl .fst .ob
  --Ren'' .Hom[_,_] = Disc
  --Ren'' .id = self _
  --Ren'' ._⋆_ (self _) (self _) = self _
  --Ren'' .⋆IdL (self _) = refl
  --Ren'' .⋆IdR (self _) = refl
  --Ren'' .⋆Assoc (self _) (self _) (self _) = refl
  --Ren'' .isSetHom = {!!}
  PreRen : Category _ _
  PreRen .ob = Cl .fst .ob → hSet (ℓ-max ℓq ℓq')
  PreRen .Hom[_,_] F₁ F₂ = (Γ : Cl .fst .ob) → ⟨ F₁ Γ ⟩ → ⟨ F₂ Γ ⟩ --(Γ : Cl .fst .ob) → f₁ Γ → f₂ Γ
  PreRen .id Γ = λ x → x
  PreRen ._⋆_ α β Γ = β Γ ∘S α Γ
  PreRen .⋆IdL α = refl
  PreRen .⋆IdR α = refl
  PreRen .⋆Assoc α β γ = refl
  PreRen .isSetHom {y = F₂} = isSetΠ2 (λ Γ _ → str (F₂ Γ))
  --nerve : Functor (Cl .fst) (PresheafCategory Ren _)
  --nerve .F-ob τ .F-ob Γ = {!Cl .fst [ Γ , τ ]!} , {!!}
  --nerve .F-ob τ .F-hom = {!!}
  --nerve .F-ob τ .F-id = {!!}
  --nerve .F-ob τ .F-seq = {!!}
  --nerve .F-hom = {!!}
  --nerve .F-id = {!!}
  --nerve .F-seq = {!!}
  --nerve' : Functor (Cl .fst) (PresheafCategory Ren' _)
  --nerve' = {!!}
  nerve : Functor (Cl .fst) PreRen
  nerve .F-ob τ Γ = Cl .fst [ Γ , τ ] , Cl .fst .isSetHom
  nerve .F-hom e Γ = λ e' → e' ⋆⟨ Cl .fst ⟩ e
  nerve .F-id = funExt (λ _ → funExt λ _ → Cl .fst .⋆IdR _)
  nerve .F-seq _ _ = funExt (λ _ → funExt (λ _ → sym (Cl .fst .⋆Assoc _ _ _)))
  PreRenᴰ : Categoryᴰ PreRen {!!} {!!}
  PreRenᴰ .Categoryᴰ.ob[_] F = (Γ : Cl .fst .ob) (e : ⟨ F Γ ⟩) → hSet {!!}
  PreRenᴰ .Categoryᴰ.Hom[_][_,_] {x = F₁} {y = F₂} α F₁ᴰ F₂ᴰ =
    (Γ : Cl .fst .ob) (e : ⟨ F₁ Γ ⟩) → ⟨ F₁ᴰ Γ e ⟩ → ⟨ F₂ᴰ Γ (α Γ e) ⟩
  PreRenᴰ .Categoryᴰ.idᴰ Γ e = λ x → x
  PreRenᴰ .Categoryᴰ._⋆ᴰ_ {f = α} {g = β} {xᴰ = F₁ᴰ} {yᴰ = F₂ᴰ} {zᴰ = F₃ᴰ} αᴰ βᴰ Γ e =
    λ eᴰ → βᴰ Γ (α Γ e) (αᴰ Γ e eᴰ)
  PreRenᴰ .Categoryᴰ.⋆IdLᴰ _ = refl
  PreRenᴰ .Categoryᴰ.⋆IdRᴰ _ = refl
  PreRenᴰ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
  PreRenᴰ .Categoryᴰ.isSetHomᴰ {yᴰ = F₂ᴰ} = isSetΠ3 (λ Γ e eᴰ → str (F₂ᴰ _ _))
  S : Section nerve PreRenᴰ
  S = {!!}
