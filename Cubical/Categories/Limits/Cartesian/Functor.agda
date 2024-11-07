{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.Cartesian.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' {- ℓS -} : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (F : Functor C D)
  where
  open Functor
  pushBinProduct' : ∀ c c' → PshHom F
    (BinProductProf _ ⟅  c ,  c' ⟆)
    (BinProductProf _ ⟅ F ⟅ c ⟆ , F ⟅ c' ⟆ ⟆)
  pushBinProduct' c c' = natTrans
        (λ _ (lift (g₁ , g₂)) → lift (F ⟪ g₁ ⟫ , F ⟪ g₂ ⟫))
        (λ f → funExt (λ _ → liftExt (≡-× (F .F-seq _ _) (F .F-seq _ _))))
  preservesBinProduct' : ∀ c c' → UniversalElement C (BinProductProf _ ⟅ c , c' ⟆) → Type _
  preservesBinProduct' c c' = preservesRepresentation F
    _
    (BinProductProf _ ⟅ F ⟅ c ⟆ , F ⟅ c' ⟆ ⟆)
    (pushBinProduct' c c')
  preservesBinProducts' : ∀ c c' → Type _
  preservesBinProducts' c c' = ∀ η → preservesBinProduct' c c' η
record CartesianFunctor (C : Category ℓC ℓC') (D : Category ℓD ℓD') : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    |F| : Functor C D
    PreservesProducts : ∀ c c' → preservesRepresentations |F|
      (BinProductProf _ ⟅ c , c' ⟆)
      (BinProductProf _ ⟅ |F| ⟅ c ⟆ , |F| ⟅ c' ⟆ ⟆)
      (pushBinProduct' |F| c c')
    PreservesTerminal : preservesTerminal _ _ |F|
--module _
--  {A : Category ℓA ℓA'}{B : Category ℓB ℓB'}
--  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
--  (F : CartesianFunctor A B)
--  (G : CartesianFunctor C D)
--  where
--  open CartesianFunctor
--  ×CF : CartesianFunctor (A ×C C) (B ×C D)
--  ×CF .|F| = (F .|F|) ×F (G .|F|)
--  ×CF .PreservesProducts (a , c) (a' , c') η (b , d) .equiv-proof ((b→Fa , d→Gc) , (b→Fa' , d→Gc')) = uniqueExists
--    ({!!} , {!!})
--    {!!}
--    {!!}

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
  -- This should "just work" by pairing "terminal" elements in the presheaves
  _×CC_ : CartesianCategory (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
  _×CC_ .fst = C×D
  _×CC_ .snd .fst = (C.𝟙 , D.𝟙) , λ (c , d) → (C.!t , D.!t) , (λ (!c , !d) → ≡-× C.𝟙η' D.𝟙η')
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
  --CBP = BinProductsToBinProducts' (C .fst) (C .snd .snd)
  --DBP = BinProductsToBinProducts' (D .fst) (D .snd .snd)
  --_×CC'_ : CartesianCategory (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
  --_×CC'_ .fst = C×D
  --_×CC'_ .snd .fst = (C.𝟙 , D.𝟙) , λ (c , d) → (C.!t , D.!t) , (λ (!c , !d) → ≡-× C.𝟙η' D.𝟙η')
  --_×CC'_ .snd .snd = BinProducts'ToBinProducts _
  --  λ ((c , d) , (c' , d')) → RepresentableToBinProduct' _
  --    (goal (c , d) (c' , d'))
  --  where
  --  goal : ((c , d) (c' , d') : C×D.ob) → UniversalElement _ (BinProductProf _ ⟅ (c , d) , (c' , d') ⟆)
  --  goal (c , d) (c' , d') .vertex = c C.×bp c' , d D.×bp d'
  --  goal (c , d) (c' , d') .element = (C.π₁ , D.π₁) , (C.π₂ , D.π₂)
  --  goal (c , d) (c' , d') .universal (c'' , d'') .equiv-proof ((f₁ , g₁) , (f₂ , g₂)) = uniqueExists
  --    (f₁ C.,p f₂ , g₁ D.,p g₂)
  --    (≡-× (≡-× C.×β₁ D.×β₁) (≡-× C.×β₂ D.×β₂))
  --    (λ a' x y → {!!})
  --    {!!}

module _
  (C : CartesianCategory ℓC ℓC')
  (D : Category ℓD ℓD')
  (F : Functor (C .fst) D)
  where
  preservesChosenBinProduct'→preservesBinProduct' : ∀ c c' →
    preservesBinProduct' F c c' (BinProductToRepresentable _ (C .snd .snd _ _)) →
    preservesBinProducts' F c c'
  preservesChosenBinProduct'→preservesBinProduct' c c' =
    preservesAnyRepresentation→preservesAllRepresentations F
    _
    (BinProductProf _ ⟅ F ⟅ c ⟆ , F ⟅ c' ⟆ ⟆)
    (pushBinProduct' F c c')
    (BinProductToRepresentable _ (C .snd .snd _ _))

module _
  {A : CartesianCategory ℓA ℓA'}{B : CartesianCategory ℓB ℓB'}
  {C : CartesianCategory ℓC ℓC'}{D : CartesianCategory ℓD ℓD'}
  (F : CartesianFunctor (A .fst) (B .fst))
  (G : CartesianFunctor (C .fst) (D .fst))
  where
  open CartesianFunctor
  ×CF : CartesianFunctor (A .fst ×C C .fst) (B .fst ×C D .fst)
  ×CF .|F| = F .|F| ×F G .|F|
  --×CF .PreservesProducts (a , c) (a' , c') η (b , d) .equiv-proof ((b→Fa , d→Gc) , (b→Fa' , d→Gc')) = uniqueExists
  --  ({!!} , {!!})
  --  {!!}
  --  {!!}
  --  {!!}
  ×CF .PreservesProducts (a , c) (a' , c') η = preservesChosenBinProduct'→preservesBinProduct'
    (A .fst ×C C .fst , {!!})
    (B .fst ×C D .fst)
    (×CF .|F|)
    (a , c)
    (a' , c')
    (λ (b , d) → record { equiv-proof = {!!} })
    η

---- test
---- TODO: this is way too painful right now with the lifts
---- see Presheaf/Morphism.agd
--module _ {C : CartesianCategory ℓC ℓC'}
--         {D : CartesianCategory ℓD ℓD'}
--         {E : CartesianCategory ℓE ℓE'}
--         (G : CartesianFunctor D E)
--         (F : CartesianFunctor C D)
--  where
--  open CartesianFunctor
--  private
--    module G = CartesianFunctor G
--    module F = CartesianFunctor F
--  _∘×F_ : CartesianFunctor C E
--  _∘×F_ .|F| = G.|F| ∘F F.|F|
--  _∘×F_ .PreservesProducts c c' = {!!}
--  _∘×F_ .PreservesTerminal = {!!}
