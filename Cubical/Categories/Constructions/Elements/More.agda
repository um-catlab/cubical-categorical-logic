{-# OPTIONS --safe #-}

-- The Category of Elements

module Cubical.Categories.Constructions.Elements.More where

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism

open import Cubical.Categories.Instances.Sets
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Constructions.Elements

import Cubical.Categories.Morphism as Morphism
import Cubical.Categories.Constructions.Slice as Slice

open import Cubical.Foundations.Isomorphism.More
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Instances.Sets.More

open Category
open Functor
open isUnivalent
module _ {ℓ ℓ'} {C : Category ℓ ℓ'} {ℓS}
                (isUnivC : isUnivalent C) (F : Functor C (SET ℓS)) where
  open Covariant {C = C}

  isUnivalent∫ : isUnivalent (∫ F)
  isUnivalent∫ .univ (c , f) (c' , f') = isIsoToIsEquiv
    ( isoToPath∫
    , (λ f≅f' → CatIso≡ _ _
        (Σ≡Prop (λ _ → (F ⟅ _ ⟆) .snd f' _)
          (cong fst
          (secEq (univEquiv isUnivC _ _) (F-Iso {F = ForgetElements F} f≅f')))))
    , λ f≡f' → ΣSquareSet (λ x → snd (F ⟅ x ⟆))
      ( cong (CatIsoToPath isUnivC) (F-pathToIso {F = ForgetElements F} f≡f')
      ∙ retEq (univEquiv isUnivC _ _) (cong fst f≡f'))) where

    isoToPath∫ : ∀ {c c' f f'}
               → CatIso (∫ F) (c , f) (c' , f')
               → (c , f) ≡ (c' , f')
    isoToPath∫ {f = f} f≅f' = ΣPathP
      ( CatIsoToPath isUnivC (F-Iso {F = ForgetElements F} f≅f')
      , toPathP ( (λ j → transport (λ i → fst
                  (F-isoToPath {F = F} isUnivC isUnivalentSET
                    (F-Iso {F = ForgetElements F} f≅f') (~ j) i)) f)
                ∙ univSetβ (F-Iso {F = F ∘F ForgetElements F} f≅f') f
                ∙ sym (f≅f' .fst .snd)))
