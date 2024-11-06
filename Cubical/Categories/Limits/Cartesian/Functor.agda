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
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.Cartesian.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓS : Level

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

module _ (C : CartesianCategory ℓC ℓC') (D : CartesianCategory ℓD ℓD') where
  open Functor
  private
    module C = CartesianCategoryNotation C
    module D = CartesianCategoryNotation D
  module _ (F : Functor (C .fst) (D .fst)) where
    preservesGivenBinProduct'→preservesBinProduct' : ∀ c c' →
      preservesBinProduct' F c c' (BinProductToRepresentable _ (C .snd .snd _ _)) →
      preservesBinProducts' F c c'
    preservesGivenBinProduct'→preservesBinProduct' c c' =
      preservesAnyRepresentation→preservesAllRepresentations F
      _
      (BinProductProf _ ⟅ F ⟅ c ⟆ , F ⟅ c' ⟆ ⟆)
      (pushBinProduct' F c c')
      (BinProductToRepresentable _ (C .snd .snd _ _))
  record CartesianFunctor : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    field
      |F| : Functor (C .fst) (D .fst)
      PreservesProducts : ∀ c c' → preservesRepresentations |F|
        (BinProductProf _ ⟅ c , c' ⟆)
        (BinProductProf _ ⟅ |F| ⟅ c ⟆ , |F| ⟅ c' ⟆ ⟆)
        (pushBinProduct' |F| c c')
      PreservesTerminal : preservesTerminal _ _ |F|

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
