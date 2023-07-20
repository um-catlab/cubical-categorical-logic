{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Slice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Morphism
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Preorder

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Categoryᴰ
open Preorderᴰ
module _ (C : Category ℓC ℓC') where
  Slices : Categoryᴰ C (ℓ-max ℓC ℓC') ℓC'
  Slices .Categoryᴰ.ob[_] c = Σ[ c' ∈ C .ob ] (C [ c' , c ])
  Slices .Categoryᴰ.Hom[_][_,_] f P Q = Σ[ fᴰ ∈ C [ P .fst , Q .fst ] ]
    f ∘⟨ C ⟩ P .snd  ≡ Q .snd ∘⟨ C ⟩ fᴰ
  Slices .Categoryᴰ.idᴰ {p} = C .id , solveCat! C
  Slices .Categoryᴰ._⋆ᴰ_ fᴰ gᴰ = fᴰ .fst ⋆⟨ C ⟩ gᴰ .fst ,
    sym (C .⋆Assoc _ _ _)
    ∙ cong₂ (seq' C) (fᴰ .snd) refl
    ∙ C .⋆Assoc _ _ _
    ∙ cong₂ (seq' C) refl (gᴰ .snd)
    ∙ sym (C .⋆Assoc _ _ _)
  Slices .Categoryᴰ.⋆IdLᴰ fᴰ =
    ΣPathPProp
      (λ _ → C .isSetHom _ _)
      (C .⋆IdL (fᴰ .fst))
  Slices .Categoryᴰ.⋆IdRᴰ fᴰ =
    ΣPathPProp (λ _ → C .isSetHom _ _) (C .⋆IdR (fᴰ .fst))
  Slices .Categoryᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ =
    ΣPathPProp (λ _ → C .isSetHom _ _) (C .⋆Assoc (fᴰ .fst) (gᴰ .fst) (hᴰ .fst))
  Slices .Categoryᴰ.isSetHomᴰ =
    isSetΣ (C .isSetHom) (λ f → isProp→isSet (C .isSetHom _ _))

  Subobjects : Preorderᴰ C (ℓ-max ℓC ℓC') ℓC'
  Subobjects .ob[_] c = Σ[ P ∈ Slices .ob[_] c ] isMonic C (P .snd)
  Subobjects .Hom[_][_,_] f P Q = Slices [ f ][ P .fst , Q .fst ]
  Subobjects .idᴰ = Slices .idᴰ
  Subobjects ._⋆ᴰ_ = Slices ._⋆ᴰ_
  Subobjects .isPropHomᴰ {yᴰ = Q} fᴰ gᴰ = Σ≡Prop (λ _ → C .isSetHom _ _)
    (Q .snd (sym (fᴰ .snd) ∙ gᴰ .snd))
