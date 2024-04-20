{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓQ ℓCᴰ ℓCᴰ' : Level

module _ (Q : ×Quiver ℓQ) where
  open ProductQuiver
  -- NOTE: I tried to make Ob opaque, but it doesn't make sense to since
  -- - You need to know the implementation to know when you can pair morphisms (equal dom)
  -- - Yes, this means Ob normalizes out when we don't always want it to, but opaque won't solve that issue
  open ×Quiver-Nice Q
  data Exp : Ob → Ob → Type ℓQ where
    -- Category
    ↑ₑ_ : ∀ t → Exp (Dom t) (Cod t)
    idₑ : ∀{Γ} → Exp Γ Γ
    _⋆ₑ_ : ∀{Γ Γ' Γ''}(δ : Exp Γ Γ') → (δ' : Exp Γ' Γ'') →  Exp Γ Γ''
    ⋆ₑIdL : ∀{Γ Δ}(δ : Exp Γ Δ) → idₑ ⋆ₑ δ ≡ δ
    ⋆ₑIdR : ∀{Γ Δ}(δ : Exp Γ Δ) → δ ⋆ₑ idₑ ≡ δ
    ⋆ₑAssoc : ∀{Γ Γ' Γ'' Γ'''}
      (δ : Exp Γ Γ')(δ' : Exp Γ' Γ'')(δ'' : Exp Γ'' Γ''')
      → (δ ⋆ₑ δ') ⋆ₑ δ'' ≡ δ ⋆ₑ (δ' ⋆ₑ δ'')
    isSetExp : ∀{Γ Γ'} → isSet (Exp Γ Γ')
    -- CartesianCategory
    -- I'd like to directly stipulate `!ₑ : ∀ Γ → isContr (Exp Γ ⊤)`
    -- but this is the best we'll get
    -- NOTE: here, we choose ! instead of just saying it merely exists
    !ₑ : ∀{Γ} → Exp Γ ⊤
    ⊤η : ∀{Γ}(t : Exp Γ ⊤) → t ≡ !ₑ
    π₁ : ∀{Γ Δ} → Exp (Γ × Δ) Γ
    π₂ : ∀{Γ Δ} → Exp (Γ × Δ) Δ
    -- and similarily, I'd like to just `isBinProduct`
    ⟨_,_⟩ : ∀{Γ Δ Δ'} → Exp Γ Δ → Exp Γ Δ' → Exp Γ (Δ × Δ')
    ×β₁ : ∀{Γ Δ Δ'}{t : Exp Γ Δ}{t' : Exp Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₁ ≡ t
    ×β₂ : ∀{Γ Δ Δ'}{t : Exp Γ Δ}{t' : Exp Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₂ ≡ t'
    ×η : ∀{Γ Δ Δ'}{t : Exp Γ (Δ × Δ')} → t ≡ ⟨ t ⋆ₑ π₁ , t ⋆ₑ π₂ ⟩

  open Category
  |FreeCartesianCategory| : Category _ _
  |FreeCartesianCategory| .ob = Ob
  |FreeCartesianCategory| .Hom[_,_] = Exp
  |FreeCartesianCategory| .id = idₑ
  |FreeCartesianCategory| ._⋆_ = _⋆ₑ_
  |FreeCartesianCategory| .⋆IdL = ⋆ₑIdL
  |FreeCartesianCategory| .⋆IdR = ⋆ₑIdR
  |FreeCartesianCategory| .⋆Assoc = ⋆ₑAssoc
  |FreeCartesianCategory| .isSetHom = isSetExp

  FreeCartesianCategory : CartesianCategory _ _
  FreeCartesianCategory .fst = |FreeCartesianCategory|
  FreeCartesianCategory .snd .fst = ⊤ , λ Γ → !ₑ , λ t → sym (⊤η t)
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.binProdOb = Γ × Δ
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.binProdPr₁ = π₁
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.binProdPr₂ = π₂
  -- this is a bit of a tedious proof I've c/p from the superceded PR draft
  -- I'm not sure anymore why we use isSet', but I'll take it
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.univProp f g = uniqueExists
    ⟨ f , g ⟩
    (×β₁ , ×β₂)
    (λ _ → isProp× (isSetExp _ _) (isSetExp _ _))
    λ ⟨f,g⟩' (comm₁ , comm₂) → cong₂ ⟨_,_⟩ (sym comm₁) (sym comm₂) ∙ sym ×η

  module _
    (CCᴰ : CartesianCategoryᴰ FreeCartesianCategory ℓCᴰ ℓCᴰ')
    where
    private
      Cᴰ = CCᴰ .fst
      module Cᴰ = Categoryᴰ Cᴰ
      termᴰ = CCᴰ .snd .fst
      bpᴰ = CCᴰ .snd .snd
      open TerminalᴰNotation _ termᴰ
      open BinProductᴰNotation bpᴰ
    open UniversalElementᴰ
    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      private
        elim-F-ob : ∀ c → Cᴰ.ob[ c ]
        elim-F-ob (↑ o)     = ı-ob o
        elim-F-ob ⊤         = 𝟙ᴰ
        elim-F-ob (c₁ × c₂) = elim-F-ob c₁ ×ᴰ elim-F-ob c₂

      module _ (ı-hom : ∀ e →
        Cᴰ.Hom[ ↑ₑ e ][ elim-F-ob (Q .snd .dom e) , elim-F-ob (Q .snd .cod e) ])
        where
        open Section
        private
          module R = HomᴰReasoning Cᴰ

          elim-F-hom : ∀ {c c'} (f : |FreeCartesianCategory| [ c , c' ]) →
            Cᴰ [ f ][ elim-F-ob c , elim-F-ob c' ]
          elim-F-hom (↑ₑ t) = ı-hom t
          elim-F-hom idₑ = Cᴰ.idᴰ
          elim-F-hom (f ⋆ₑ g) = elim-F-hom f Cᴰ.⋆ᴰ elim-F-hom g
          elim-F-hom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elim-F-hom f) i
          elim-F-hom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elim-F-hom f) i
          elim-F-hom (⋆ₑAssoc f g h i) =
            Cᴰ.⋆Assocᴰ (elim-F-hom f) (elim-F-hom g) (elim-F-hom h) i
          elim-F-hom (isSetExp f g p q i j) =
            isOfHLevel→isOfHLevelDep 2 (λ _ → Cᴰ.isSetHomᴰ)
            (elim-F-hom f) (elim-F-hom g)
            (cong elim-F-hom p) (cong elim-F-hom q)
            (isSetExp f g p q)
            i j
          elim-F-hom !ₑ = !tᴰ _
          -- TODO: Why does this need rectify?
          elim-F-hom (⊤η f i) =
            R.≡[]-rectify {p' = ⊤η f} (𝟙ηᴰ (elim-F-hom f)) i
          elim-F-hom π₁ = π₁ᴰ
          elim-F-hom π₂ = π₂ᴰ
          elim-F-hom ⟨ f₁ , f₂ ⟩ = elim-F-hom f₁ ,pᴰ elim-F-hom f₂
          elim-F-hom (×β₁ {t = f₁}{t' = f₂} i) =
            ×β₁ᴰ {f₁ᴰ = elim-F-hom f₁} {f₂ᴰ = elim-F-hom f₂} i
          elim-F-hom (×β₂ {t = f₁}{t' = f₂} i) =
            ×β₂ᴰ {f₁ᴰ = elim-F-hom f₁} {f₂ᴰ = elim-F-hom f₂} i
          -- TODO: Why do we need this rectify too?
          elim-F-hom (×η {t = f} i) =
            R.≡[]-rectify {p' = ×η {t = f}} (×ηᴰ {fᴰ = elim-F-hom f}) i

        elim : Section Cᴰ
        elim .F-ob = elim-F-ob
        elim .F-hom = elim-F-hom
        elim .F-id = refl
        elim .F-seq _ _ = refl
