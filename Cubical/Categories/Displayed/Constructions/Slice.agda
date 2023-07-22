{-
  The slice category over a functor, viewed as a displayed category
  over the domain.
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Slice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Functor

open import Cubical.Tactics.CategorySolver.Reflection
open import Cubical.Tactics.FunctorSolver.Reflection

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Categoryᴰ
open Functor

module _ (C : Category ℓC ℓC') {D : Category ℓD ℓD'} (p : Functor D C) where
  _/C_ : Categoryᴰ C (ℓ-max ℓC' ℓD) (ℓ-max ℓC' ℓD')
  _/C_ .ob[_] x = Σ[ d ∈ D .ob ] (C [ x , p ⟅ d ⟆ ])
  _/C_ .Hom[_][_,_] f xᴰ yᴰ = Σ[ g ∈ D [ xᴰ .fst , yᴰ .fst ] ]
    p ⟪ g ⟫ ∘⟨ C ⟩ xᴰ .snd ≡ yᴰ .snd ∘⟨ C ⟩ f
  _/C_ .idᴰ = (D .id) , solveFunctor! D C p
  _/C_ ._⋆ᴰ_ fᴰ gᴰ = (fᴰ .fst ⋆⟨ D ⟩ gᴰ .fst) ,
    cong₂ (comp' C) (p .F-seq _ _) refl
    ∙ sym (C .⋆Assoc _ _ _)
    ∙ cong₂ (comp' C) refl (fᴰ .snd)
    ∙ C .⋆Assoc _ _ _
    ∙ cong₂ (comp' C) (gᴰ .snd) refl
    ∙ sym (C .⋆Assoc _ _ _)
  _/C_ .⋆IdLᴰ fᴰ = ΣPathPProp (λ _ → C .isSetHom _ _) (D .⋆IdL _)
  _/C_ .⋆IdRᴰ fᴰ = ΣPathPProp (λ _ → C .isSetHom _ _) (D .⋆IdR _)
  _/C_ .⋆Assocᴰ fᴰ gᴰ hᴰ = ΣPathPProp (λ _ → C .isSetHom _ _) (D .⋆Assoc _ _ _)
  _/C_ .isSetHomᴰ =
    isSetΣ (D .isSetHom) (λ _ → isProp→isSet (C .isSetHom _ _))

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where
  open Functorᴰ
  cod : Functorᴰ Id D (C /C (Fst {Cᴰ = D}))
  cod .F-obᴰ x = (_ , x) , C .id
  cod .F-homᴰ fᴰ = (_ , fᴰ) , solveCat! C
  cod .F-idᴰ = ΣPathPProp (λ _ → C .isSetHom _ _) refl
  cod .F-seqᴰ fᴰ gᴰ = ΣPathPProp (λ _ → C .isSetHom _ _) refl
