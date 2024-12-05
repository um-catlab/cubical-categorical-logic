{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Cartesian.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Presheaf
open import Cubical.Data.Sigma

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

CartesianCategory : (ℓ ℓ' : Level) → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
CartesianCategory ℓ ℓ' = Σ[ C ∈ Category ℓ ℓ' ] Terminal C × BinProducts C

module CartesianCategoryNotation (CC : CartesianCategory ℓC ℓC') where
  private
    C = CC .fst
  open Category C public
  open Notation C (CC .snd .snd) renaming (_×_ to _×bp_) public
  open TerminalNotation C (CC .snd .fst) public

  unitor-l : ∀ {a} → CatIso C (𝟙 ×bp a) a
  unitor-l .fst = π₂
  unitor-l .snd .isIso.inv = !t ,p id
  unitor-l .snd .isIso.sec = ×β₂
  unitor-l .snd .isIso.ret =
    ,p-natural ∙ cong₂ _,p_ 𝟙η' (⋆IdR _ ∙ sym (⋆IdL _)) ∙ sym ×η

  CCTerminal' : Terminal' C
  CCTerminal' = terminalToUniversalElement (CC .snd .fst)

  CCBinProducts' : BinProducts' C
  CCBinProducts' = BinProductsToBinProducts' _ (CC .snd .snd)

  CCBinProducts'' : ∀ c c' → UniversalElement _ (BinProductProf C ⟅ c , c' ⟆)
  CCBinProducts'' c c' = BinProductToRepresentable _ (CC .snd .snd c c')

-- the product of two cartesian categories is cartesian
module _
  (C : CartesianCategory ℓC ℓC')
  (D : CartesianCategory ℓD ℓD')
  where
  open BinProduct
  private
    C×D = C .fst ×C D .fst
    module C×D = Category C×D
    module C = CartesianCategoryNotation C
    module D = CartesianCategoryNotation D
  -- TODO: this is a very manual definition for BinProducts
  -- This should "just work" by pairing "terminal" elements,
  -- viewing presheafs as displayed over the indexing category
  -- But it seems like a sidetrack to do it right now
  _×CC_ : CartesianCategory (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
  _×CC_ .fst = C×D
  _×CC_ .snd .fst = (C.𝟙 , D.𝟙) , λ _ → (C.!t , D.!t) , (λ _ → ≡-× C.𝟙η' D.𝟙η')
  _×CC_ .snd .snd (c , d) (c' , d') .binProdOb = (c C.×bp c') , (d D.×bp d')
  _×CC_ .snd .snd (c , d) (c' , d') .binProdPr₁ = C.π₁ , D.π₁
  _×CC_ .snd .snd (c , d) (c' , d') .binProdPr₂ = C.π₂ , D.π₂
  _×CC_ .snd .snd (c , d) (c' , d') .univProp f g = uniqueExists
    (f .fst C.,p g .fst , f .snd D.,p g .snd)
    (≡-× C.×β₁ D.×β₁ , ≡-× C.×β₂ D.×β₂)
    (λ _ _ _ → ≡-× (C×D.isSetHom _ _ _ _) (C×D.isSetHom _ _ _ _))
    λ _ (p , q) → ≡-×
      (C.×-extensionality (C.×β₁ ∙ congS fst (sym p)) (C.×β₂ ∙ congS fst (sym q)))
      (D.×-extensionality (D.×β₁ ∙ congS snd (sym p)) (D.×β₂ ∙ congS snd (sym q)))
