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
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' {- ℓS -} : Level

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
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

-- having structure shouldn't be necessary for C and D to preserve it
-- although if C does, it's sufficient to preserve the (chosen) structure
record CartesianFunctor (C : Category ℓC ℓC') (D : Category ℓD ℓD') : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    |F| : Functor C D
    -- TODO: this seems okay, but maybe isn't quite a BinProduct'
    PreservesProducts : ∀ c c' → preservesRepresentations |F|
      (BinProductProf _ ⟅ c , c' ⟆)
      (BinProductProf _ ⟅ |F| ⟅ c ⟆ , |F| ⟅ c' ⟆ ⟆)
      (pushBinProduct' |F| c c')
    -- just reusing what's there
    PreservesTerminal : preservesTerminals _ _ |F|

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

-- probably useless helpers in case the domain of a cartesian functor is cartesian
module _
  (C : CartesianCategory ℓC ℓC')
  (D : Category ℓD ℓD')
  (F : Functor (C .fst) D)
  where
  private
    module C = CartesianCategoryNotation C
  preservesChosenBinProduct'→preservesBinProduct' : ∀ c c' →
    preservesBinProduct' F c c' (BinProductToRepresentable _ (C .snd .snd _ _)) →
    preservesBinProducts' F c c'
  preservesChosenBinProduct'→preservesBinProduct' c c' =
    preservesAnyRepresentation→preservesAllRepresentations F
    _
    (BinProductProf _ ⟅ F ⟅ c ⟆ , F ⟅ c' ⟆ ⟆)
    (pushBinProduct' F c c')
    (BinProductToRepresentable _ (C .snd .snd _ _))

  preservesChosenTerminal→PreservesTerminal : isTerminal D (F ⟅ C.𝟙 ⟆) →
    preservesTerminals (C .fst) D F
  preservesChosenTerminal→PreservesTerminal =
    preserveAnyTerminal→PreservesTerminals (C .fst) D F (C .snd .fst)

-- the pairing of two cartesian functors is cartesian,
-- made easier assuming everything is cartesian?
-- Or maybe that assumption isn't useful
module _
  {A : CartesianCategory ℓA ℓA'}{B : CartesianCategory ℓB ℓB'}
  {C : CartesianCategory ℓC ℓC'}{D : CartesianCategory ℓD ℓD'}
  (F : CartesianFunctor (A .fst) (B .fst))
  (G : CartesianFunctor (C .fst) (D .fst))
  where
  open CartesianFunctor
  private
    module A = CartesianCategoryNotation A
    module C = CartesianCategoryNotation C
    module A×C = CartesianCategoryNotation (A ×CC C)
    module B×D = CartesianCategoryNotation (B ×CC D)
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
  ×CF .PreservesTerminal =
    preserveAnyTerminal→PreservesTerminals ((A ×CC C) .fst) ((B ×CC D) .fst)
      (F .|F| ×F G .|F|) ((A ×CC C) .snd .fst)
      (λ _ → (F-preserves _ .fst , G-preserves _ .fst) , λ _ → ≡-× (F-preserves _ .snd _) (G-preserves _ .snd _))
      where
      F-preserves : isTerminal (B .fst) (F .|F| ⟅ A.𝟙 ⟆)
      F-preserves = F .PreservesTerminal (A .snd .fst)
      G-preserves : isTerminal (D .fst) (G .|F| ⟅ C.𝟙 ⟆)
      G-preserves = G .PreservesTerminal (C .snd .fst)

-- TODO: compose cartesian functors
-- Right now, this would just be to test that the definition
-- is "right"
-- But this is way too painful to do right now with the lifts
-- see Presheaf/Morphism.agda
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
