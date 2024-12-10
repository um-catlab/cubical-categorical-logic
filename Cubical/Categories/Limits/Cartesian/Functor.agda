{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.Cartesian.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
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
import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.BinProduct.Cartesian

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
    PreservesBinProducts : ∀ c c' → preservesRepresentations |F|
      (BinProductProf _ ⟅ c , c' ⟆)
      (BinProductProf _ ⟅ |F| ⟅ c ⟆ , |F| ⟅ c' ⟆ ⟆)
      (pushBinProduct' |F| c c')
    -- just reusing what's there
    PreservesTerminal : preservesTerminals _ _ |F|

module _ {C : CartesianCategory ℓC ℓC'} where
  open CartesianFunctor
  open UniversalElement
  IdCF : CartesianFunctor (C .fst) (C .fst)
  IdCF .|F| = Id
  IdCF .PreservesBinProducts _ _ = universal
  IdCF .PreservesTerminal = snd

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

-- probably useless helpers in case the domain of a cartesian functor is cartesian
module _
  (C : CartesianCategory ℓC ℓC')
  (D : Category ℓD ℓD')
  (F : Functor (C .fst) D)
  where
  private
    module C = CartesianCategoryNotation C
  preservesAnyBinProduct'→preservesBinProduct' : ∀ c c' →
    (bp : UniversalElement (C .fst) (BinProductProf _ ⟅ c , c' ⟆)) →
    preservesBinProduct' F c c' bp →
    preservesBinProducts' F c c'
  preservesAnyBinProduct'→preservesBinProduct' c c' =
    preservesAnyRepresentation→preservesAllRepresentations F
    (BinProductProf _ ⟅ c , c' ⟆)
    (BinProductProf _ ⟅ F ⟅ c ⟆ , F ⟅ c' ⟆ ⟆)
    (pushBinProduct' F c c')

-- the pairing of two cartesian functors is cartesian,
-- made easier assuming everything is cartesian?
-- Or maybe that assumption isn't useful
module _
  {A : CartesianCategory ℓA ℓA'}
  {B : Category ℓB ℓB'}
  {C : Category ℓC ℓC'}
  (F : CartesianFunctor (A .fst) B)
  (G : CartesianFunctor (A .fst) C)
  where
  open CartesianFunctor
  private
    module A = CartesianCategoryNotation A
    module B×C = Category  (B BP.×C C)
  -- TODO: using _,F_ right now requires explicitly specifying A, since F and G don't depend on A .snd
  _,F_ : CartesianFunctor (A .fst) (B BP.×C C)
  _,F_ .|F| = F .|F| BP.,F G .|F|
  _,F_ .PreservesBinProducts a a' = preservesAnyBinProduct'→preservesBinProduct'
    A
    (B BP.×C C)
    (_,F_ .|F| )
    _
    _
    (BinProductToRepresentable _ (A .snd .snd _ _))
    goal
    where
    goal : isUniversal (B BP.×C C)
      (BinProductProf _ ⟅ _,F_ .|F| ⟅ a ⟆ , _,F_ .|F| ⟅ a' ⟆ ⟆)
      ((F .|F| ⟅ a A.×bp a' ⟆ , G .|F| ⟅ a A.×bp a' ⟆))
      ((F .|F| ⟪ A.π₁ ⟫ , G .|F| ⟪ A.π₁ ⟫) , (F .|F| ⟪ A.π₂ ⟫ , G .|F| ⟪ A.π₂ ⟫))
    goal (b , c) .equiv-proof ((f , f') , (g , g')) = uniqueExists
      (f,g , f',g')
      (≡-× (≡-× (congS fst F-β) (congS fst G-β)) (≡-× (congS snd F-β) (congS snd G-β)))
      (λ _ → isSet× B×C.isSetHom B×C.isSetHom _ _)
      λ (h , h') p → ≡-×
        (cong fst (F-η (h , ≡-× (congS (fst ∘S fst) p) (congS (fst ∘S snd) p))))
        (cong fst (G-η (h' , ≡-× (cong (snd ∘S fst) p) (congS (snd ∘S snd) p))))
      where
      F-preserves : isUniversal B (BinProductProf _ ⟅ F .|F| ⟅ a ⟆ , F .|F| ⟅ a' ⟆ ⟆) _ _
      F-preserves = F .PreservesBinProducts a a' (BinProductToRepresentable (A .fst) (A .snd .snd _ _))
      f,g = F-preserves b .equiv-proof (f , g) .fst .fst
      F-β = F-preserves b .equiv-proof (f , g) .fst .snd
      F-η = F-preserves b .equiv-proof (f , g) .snd
      G-preserves : isUniversal C (BinProductProf _ ⟅ G .|F| ⟅ a ⟆ , G .|F| ⟅ a' ⟆ ⟆) _ _
      G-preserves = G .PreservesBinProducts a a' (BinProductToRepresentable (A .fst) (A .snd .snd _ _))
      f',g' = G-preserves c .equiv-proof (f' , g') .fst .fst
      G-β = G-preserves c .equiv-proof (f' , g') .fst .snd
      G-η = G-preserves c .equiv-proof (f' , g') .snd
  _,F_ .PreservesTerminal = preserveAnyTerminal→PreservesTerminals
    (A .fst)
    (B BP.×C C)
    (_,F_ .|F|)
    (A .snd .fst)
    λ _ → (F-preserves _ .fst , G-preserves _ .fst) , λ _ → ≡-× (F-preserves _ .snd _) (G-preserves _ .snd _)
    where
    F-preserves : isTerminal B (F .|F| ⟅ A.𝟙 ⟆)
    F-preserves = F .PreservesTerminal (A .snd .fst)
    G-preserves : isTerminal C (G .|F| ⟅ A.𝟙 ⟆)
    G-preserves = G .PreservesTerminal (A .snd .fst)
-- TODO: this should be defined as the composition of ,F and the projections,
-- but we don't need this right now and would need composition of cartesian
-- functors first, which requires modifying the morphism of presheaf stuff to
-- not require lifts
-- Although this is technically useable since the underlying functor is just BP.×F
-- it just duplicates the above proof essentially
module _
  {A : CartesianCategory ℓA ℓA'}{B : Category ℓB ℓB'}
  {C : CartesianCategory ℓC ℓC'}{D : Category ℓD ℓD'}
  (F : CartesianFunctor (A .fst) B)
  (G : CartesianFunctor (C .fst) D)
  where
  open CartesianFunctor
  private
    module A = CartesianCategoryNotation A
    module C = CartesianCategoryNotation C
    module A×C = CartesianCategoryNotation (A ×C C)
    module B×D = Category (B BP.×C D)
  -- TODO: same thing about implicit argumens here
  _×F_ : CartesianFunctor (A .fst BP.×C C .fst) (B BP.×C D)
  _×F_ .|F| = F .|F| BP.×F G .|F|
  _×F_ .PreservesBinProducts (a , c) (a' , c') = preservesAnyBinProduct'→preservesBinProduct'
    (A ×C C)
    (B BP.×C D)
    (_×F_ .|F|)
    _
    _
    (BinProductToRepresentable _ ((A ×C C) .snd .snd _ _))
    goal
    where
    goal : isUniversal (B BP.×C D)
      (BinProductProf _ ⟅ _×F_ .|F| ⟅ a , c ⟆ , _×F_ .|F| ⟅ a' , c' ⟆ ⟆)
      (F .|F| ⟅ a A.×bp a' ⟆ , G .|F| ⟅ c C.×bp c' ⟆)
      ((F .|F| ⟪ A.π₁ ⟫ , G .|F| ⟪ C.π₁ ⟫) , (F .|F| ⟪ A.π₂ ⟫ , G .|F| ⟪ C.π₂ ⟫))
    goal (b , d) .equiv-proof ((f₁ , g₁) , (f₂ , g₂)) =
      uniqueExists
      (F-preserves b .equiv-proof (f₁ , f₂) .fst .fst , G-preserves d .equiv-proof (g₁ , g₂) .fst .fst)
      (≡-× (≡-× (congS fst F-β) (congS fst G-β)) (≡-× (congS snd F-β) (congS snd G-β)))
      (λ _ → isSet× B×D.isSetHom B×D.isSetHom _ _)
      λ (h , h') p → ≡-×
        (congS fst (F-preserves b .equiv-proof (f₁ , f₂) .snd (h , ≡-× (congS (fst ∘S fst) p) (congS (fst ∘S snd) p))))
        (congS fst (G-preserves d .equiv-proof (g₁ , g₂) .snd (h' , (≡-× (congS (snd ∘S fst) p) (congS (snd ∘S snd) p)))))
      where
      F-preserves : isUniversal B (BinProductProf _ ⟅ F .|F| ⟅ a ⟆ , F .|F| ⟅ a' ⟆ ⟆) _ _
      F-preserves = F .PreservesBinProducts a a' (BinProductToRepresentable (A .fst) (A .snd .snd _ _))
      F-β = F-preserves b .equiv-proof (f₁ , f₂) .fst .snd
      G-preserves : isUniversal D (BinProductProf _ ⟅ G .|F| ⟅ c ⟆ , G .|F| ⟅ c' ⟆ ⟆) _ _
      G-preserves = G .PreservesBinProducts c c' (BinProductToRepresentable (C .fst) (C .snd .snd _ _))
      G-β = G-preserves d .equiv-proof (g₁ , g₂) .fst .snd
  _×F_ .PreservesTerminal =
    preserveAnyTerminal→PreservesTerminals ((A ×C C) .fst) (B BP.×C D)
    (_×F_ .|F|) ((A ×C C) .snd .fst)
    (λ _ → (F-preserves _ .fst , G-preserves _ .fst) , λ _ → ≡-× (F-preserves _ .snd _) (G-preserves _ .snd _))
    where
    F-preserves : isTerminal B (F .|F| ⟅ A.𝟙 ⟆)
    F-preserves = F .PreservesTerminal (A .snd .fst)
    G-preserves : isTerminal D (G .|F| ⟅ C.𝟙 ⟆)
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
