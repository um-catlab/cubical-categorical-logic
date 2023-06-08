{-# OPTIONS --safe #-}

module Cubical.Categories.Adjoint.Monad where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties

open import Cubical.Categories.NaturalTransformation.More

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
         (L : Functor C D) (R : Functor D C) where
  open UnitCounit
  open IsMonad
  open _⊣_
  open NatIso
  open Category
  open NatTrans
  open Functor

  MonadFromAdjunction : (L ⊣ R) → IsMonad (R ∘F L)
  η (MonadFromAdjunction L⊣R) =  L⊣R .η
  N-ob (μ (MonadFromAdjunction L⊣R)) c = R ⟪ L⊣R .ε ⟦ L ⟅ c ⟆ ⟧ ⟫
  N-hom (μ (MonadFromAdjunction L⊣R)) f = (R ∘ʳ ((L⊣R .ε) ∘ˡ L)) .N-hom f
  idl-μ (MonadFromAdjunction L⊣R) =
    makeNatTransPathP
      (λ i → F-rUnit i)
      (λ i → funcComp R L)
      (funExt (λ c → L⊣R .Δ₂ (L ⟅ c ⟆)))
  idr-μ (MonadFromAdjunction L⊣R) =
    makeNatTransPathP
      (λ i → F-lUnit i)
      (λ i → funcComp R L)
      (funExt (λ c →
        compTrans (μ (MonadFromAdjunction L⊣R)) (funcComp R L ∘ʳ L⊣R .η) .N-ob c
          ≡⟨ refl ⟩
        (funcComp R L) ⟪ L⊣R .η ⟦ c ⟧ ⟫ ⋆⟨ C ⟩ R ⟪ L⊣R .ε ⟦ L ⟅ c ⟆ ⟧ ⟫
          ≡⟨ sym (R .F-seq (L ⟪ L⊣R .η ⟦ c ⟧ ⟫) (L⊣R .ε ⟦ L ⟅ c ⟆ ⟧)) ⟩
        R ⟪ (L ⟪ L⊣R .η ⟦ c ⟧ ⟫) ⋆⟨ D ⟩ (L⊣R .ε ⟦ L ⟅ c ⟆ ⟧) ⟫
          ≡⟨ ((λ i → R ⟪ L⊣R .Δ₁ c i ⟫)) ⟩
        R ⟪ D .id ⟫
          ≡⟨ R .F-id ⟩
        C .id ∎))
  assoc-μ (MonadFromAdjunction L⊣R) =
    makeNatTransPathP
      (λ i → F-assoc i)
      (λ i → funcComp R L)
      (funExt (λ c →
        (funcComp R L) ⟪ R ⟪ L⊣R .ε ⟦ L ⟅ c ⟆ ⟧ ⟫ ⟫
          ⋆⟨ C ⟩ R ⟪ L⊣R .ε ⟦ L ⟅ c ⟆ ⟧ ⟫
          ≡⟨ sym (R .F-seq (L ⟪ R ⟪ L⊣R .ε ⟦ L ⟅ c ⟆ ⟧ ⟫ ⟫)
             (L⊣R .ε ⟦ L ⟅ c ⟆ ⟧)) ⟩
        R ⟪ (L ⟪ R ⟪ L⊣R .ε ⟦ L ⟅ c ⟆ ⟧ ⟫ ⟫) ⋆⟨ D ⟩ (L⊣R .ε ⟦ L ⟅ c ⟆ ⟧) ⟫
          ≡⟨ (λ i → R ⟪ L⊣R .ε .N-hom (L⊣R .ε .N-ob (L ⟅ c ⟆)) i ⟫) ⟩
        R ⟪ L⊣R .ε ⟦ L ⟅ funcComp R L ⟅ c ⟆ ⟆ ⟧ ⋆⟨ D ⟩ L⊣R .ε ⟦ L ⟅ c ⟆ ⟧ ⟫
          ≡⟨ R .F-seq (L⊣R .ε ⟦ L ⟅ funcComp R L ⟅ c ⟆ ⟆ ⟧)
            (L⊣R .ε ⟦ L ⟅ c ⟆ ⟧) ⟩
        R ⟪ L⊣R .ε ⟦ L ⟅ funcComp R L ⟅ c ⟆ ⟆ ⟧ ⟫ ⋆⟨ C ⟩
          R ⟪ L⊣R .ε ⟦ L ⟅ c ⟆ ⟧ ⟫ ∎
      ))
