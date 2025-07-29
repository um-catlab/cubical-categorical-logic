{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Sets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Displayed.Base

open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓC ℓC' ℓD ℓD' : Level

open UniversalElementᴰ
open UniversalElementⱽ
open CartesianLift
open Categoryᴰ
open isIsoOver

isFibrationSETᴰ : isFibration (SETᴰ ℓ ℓ')
isFibrationSETᴰ {c = A}{c' = B} Bᴰ f .f*yᴰ a = Bᴰ (f a)
isFibrationSETᴰ cᴰ' f .CartesianLift.π = λ x z → z
isFibrationSETᴰ cᴰ' f .isCartesian .fst = λ z₁ → z₁
isFibrationSETᴰ cᴰ' f .isCartesian .snd .fst _ = refl
isFibrationSETᴰ cᴰ' f .isCartesian .snd .snd _ = refl

hasVerticalTerminals : hasAllTerminalⱽ (SETᴰ ℓ ℓ')
hasVerticalTerminals A .vertexⱽ a = Unit* , isSetUnit*
hasVerticalTerminals A .elementⱽ = tt
hasVerticalTerminals A .universalⱽ .fst = λ _ x _ → tt*
hasVerticalTerminals A .universalⱽ .snd .fst b = refl
hasVerticalTerminals A .universalⱽ .snd .snd a = refl

module _ {A : hSet ℓ} (Aᴰ₁ Aᴰ₂ : ⟨ A ⟩ → hSet ℓ') where
  open Functorᴰ
  private
    module Aᴰ₁×Aᴰ₂ = PresheafⱽNotation (BinProductProfⱽ (SETᴰ ℓ ℓ') .F-obᴰ {A} (Aᴰ₁ , Aᴰ₂))
  Aᴰ₁×Aᴰ₂ : ⟨ A ⟩ → hSet ℓ'
  Aᴰ₁×Aᴰ₂ a = (⟨ Aᴰ₁ a ⟩ × ⟨ Aᴰ₂ a ⟩) , (isSet× (Aᴰ₁ a .snd) (Aᴰ₂ a .snd))

  -- the transports here are caused by the fact that vertical
  -- composition is defined using reindexing :/ the only way to avoid
  -- this would be to "fatten" the definition of displayed categories to
  -- include the "redundant" vertical and heterogeneous compositions
  -- then in the case of nice examples like SETᴰ (and possibly
  -- PRESHEAFᴰ) we would get that there is no transport required
  opaque
    -- this refactor is a great example of why opaque expression
    -- syntax would be extremely helpful
    SETᴰVerticalBinProd-section :
      ∀ (B : hSet ℓ)(Bᴰ : ⟨ B ⟩ → hSet ℓ')(f : SET ℓ [ B , A ]) →
      section {A = ∀ b → ⟨ Bᴰ b ⟩ →  ⟨ Aᴰ₁ (f b) ⟩ × ⟨ Aᴰ₂ (f b) ⟩ }
        (λ fᴰ → Aᴰ₁×Aᴰ₂._⋆ᴰⱽ_ {x = B}{xᴰ = Bᴰ}{cᴰ = Aᴰ₁×Aᴰ₂} fᴰ ((λ _ r → fst r) , (λ _ r → snd r)))
        (λ (f₁ , f₂) a aᴰ → f₁ _ aᴰ , f₂ _ aᴰ)
    SETᴰVerticalBinProd-section B Bᴰ f (f₁ , f₂) = sym $ transport-filler _ _

    SETᴰVerticalBinProd-retract :
      ∀ (B : hSet ℓ)(Bᴰ : ⟨ B ⟩ → hSet ℓ')(f : SET ℓ [ B , A ]) →
        retract {A = ∀ b → ⟨ Bᴰ b ⟩ →  ⟨ Aᴰ₁ (f b) ⟩ × ⟨ Aᴰ₂ (f b) ⟩ }
        (λ fᴰ → Aᴰ₁×Aᴰ₂._⋆ᴰⱽ_ {x = B}{xᴰ = Bᴰ}{cᴰ = Aᴰ₁×Aᴰ₂} fᴰ ((λ _ r → fst r) , (λ _ r → snd r)))
        (λ (f₁ , f₂) a aᴰ → f₁ _ aᴰ , f₂ _ aᴰ)
    SETᴰVerticalBinProd-retract B Bᴰ f a = funExt₂ λ b bᴰ →
      ΣPathP
       ( fromPathP (λ i → a
           (transport-filler (λ _ → ⟨ B ⟩) b (~ i))
           (transport-filler (λ j₂ → fst (Bᴰ (transp (λ j₁ → fst B) (~ j₂) b)))
             bᴰ (~ i)) .fst)
       , fromPathP
         (λ i → a
           (transport-filler (λ _ → ⟨ B ⟩) b (~ i))
           (transport-filler (λ j₂ → fst (Bᴰ (transp (λ j₁ → fst B) (~ j₂) b)))
             bᴰ (~ i)) .snd))


  SETᴰVerticalBinProd : BinProductⱽ (SETᴰ ℓ ℓ') {c = A} (Aᴰ₁ , Aᴰ₂)
  SETᴰVerticalBinProd .vertexⱽ = Aᴰ₁×Aᴰ₂
  SETᴰVerticalBinProd .elementⱽ = (λ _ → fst) , (λ _ → snd)
  SETᴰVerticalBinProd .universalⱽ .fst (f₁ , f₂) a aᴰ = f₁ _ aᴰ , f₂ _ aᴰ
  SETᴰVerticalBinProd .universalⱽ {y} {yᴰ} {f} .snd .fst =
    SETᴰVerticalBinProd-section y yᴰ f
  SETᴰVerticalBinProd .universalⱽ {y} {yᴰ} {f} .snd .snd =
    SETᴰVerticalBinProd-retract y yᴰ f

hasVerticalBinProds : hasAllBinProductⱽ (SETᴰ ℓ ℓ')
hasVerticalBinProds (A₁ , A₂) = SETᴰVerticalBinProd A₁ A₂

SETᴰCartesianCategoryⱽ :
  ∀ ℓ ℓ' → CartesianCategoryⱽ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
SETᴰCartesianCategoryⱽ ℓ ℓ' .fst = SETᴰ ℓ ℓ'
SETᴰCartesianCategoryⱽ ℓ ℓ' .snd .fst = isFibrationSETᴰ
SETᴰCartesianCategoryⱽ ℓ ℓ' .snd .snd .fst = hasVerticalTerminals
SETᴰCartesianCategoryⱽ ℓ ℓ' .snd .snd .snd = hasVerticalBinProds
