{-# OPTIONS --safe #-}
module Cubical.Categories.DistributiveLaw.ComonadOverMonad.BiKleisli.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Comonad.Base

open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.Base
open import Cubical.Tactics.FunctorSolver.Reflection
private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'}
         (D : Comonad C)
         (T : Monad C) (law : DistributiveLaw D T) where
  open NatTrans
  open IsComonad (D .snd)
  open IsMonad (T .snd)
  open IsDistributiveLaw (law .snd)
  open Category C
  open Functor
  bind' : ∀ {c d} → Hom[ c , T .fst ⟅ d ⟆ ] → Hom[ T .fst ⟅ c ⟆ , T .fst ⟅ d ⟆ ]
  bind' {c}{d} f = bind .N-ob _ f

  l = law .fst

  -- TODO: move this upstream
  bind-η : ∀ {c} → bind' (η ⟦ c ⟧) ≡ id
  bind-η = λ i → idr-μ i ⟦ _ ⟧

  private
    variable
      x y z : ob
      k k' : Hom[ x , y ]

  -- Category with the same objects but morphisms are C [ D x , T y ]
  BiKleisli : Category ℓ ℓ'
  BiKleisli .Category.ob = ob
  BiKleisli .Category.Hom[_,_] x y = Hom[ D .fst ⟅ x ⟆ , T .fst ⟅ y ⟆  ]
  BiKleisli .Category.isSetHom = isSetHom
  BiKleisli .Category.id {x} = (η ∘ᵛ ε) ⟦ x ⟧
  BiKleisli .Category._⋆_ f g = bind' g ∘ (l ⟦ _ ⟧ ∘ extend f)
  BiKleisli .Category.⋆IdL f =
  -- δ ⋆ D (ε ⋆ η) ⋆ l ⋆ T f ⋆ μ
    cong₂ _∘_ refl (cong₂ _∘_ refl ((cong₂ _∘_ (D .fst .F-seq _ _) refl)
                                   ∙ sym (⋆Assoc _ _ _)
                                   ∙ cong₂ _∘_ refl extend-ε
                                   ∙ ⋆IdL _))
  -- T η ⋆ l ⋆ T f ⋆ μ
    ∙ cong₂ _∘_ refl η-law
  -- η ⋆ T f ⋆ μ
    ∙ sym (⋆Assoc _ _ _)
    ∙ cong₂ _∘_ refl (sym (η .N-hom f))
  -- f ⋆ η * μ
    ∙ ⋆Assoc _ _ _
    ∙ cong₂ _∘_ (λ i → idl-μ i ⟦ _ ⟧) refl
    ∙ ⋆IdR f
  BiKleisli .Category.⋆IdR f =
  -- δ ⋆ D f ⋆ l ⋆ T (ε ⋆ η) ⋆ μ
    cong₂ _∘_ (cong₂ _∘_ refl (T .fst .F-seq _ _)
              ∙ ⋆Assoc _ _ _ ∙ cong₂ _∘_ (λ i → idr-μ i ⟦ _ ⟧) refl
              ∙ ⋆IdR _)
              refl
  -- δ ⋆ D f ⋆ l ⋆ T ε
  -- δ ⋆ D f ⋆ l ⋆ T ε
    ∙ ⋆Assoc _ _ _
    ∙ cong₂ _∘_ ε-law refl
  -- δ ⋆ D f ⋆ ε
    ∙ ⋆Assoc _ _ _
    ∙ cong₂ _∘_ (ε .N-hom _) refl
  -- f ⋆ δ ⋆ ε
    ∙ (sym (⋆Assoc _ _ _) ∙ cong₂ _∘_ refl (λ i → idl-δ i ⟦ _ ⟧))
    ∙ ⋆IdL _
  BiKleisli .Category.⋆Assoc f g h =
    -- δ ⋆ D (δ ⋆ D f ⋆ l ⋆ T g ⋆ μ) ⋆ l ⋆ T h ⋆ μ
    (cong₂ _⋆_ (cong₂ _⋆_ (cong₂ _⋆_ refl (D .fst .F-seq _ _ ∙
      cong₂ _⋆_ (D .fst .F-seq _ _ ∙ cong₂ _⋆_ (D .fst .F-seq _ _) refl)
        (D .fst .F-seq _ _))) refl) refl)
    -- δ ⋆ D δ ⋆ DD f ⋆ D l ⋆ D T g ⋆ D μ ⋆ l ⋆ T h ⋆ μ
    ∙ cong₂ _⋆_ (cong₂ _⋆_ (sym (⋆Assoc _ _ _) ∙
      cong₂ _⋆_ (sym (⋆Assoc _ _ _) ∙ cong₂ _⋆_ (sym (⋆Assoc _ _ _) ∙
        cong₂ _∘_ refl assoc-δ) refl) refl) refl) refl
    -- δ ⋆ δ ⋆ DD f ⋆ D l ⋆ D T g ⋆ D μ ⋆ l ⋆ T h ⋆ μ
    ∙ cong₂ _∘_ refl (cong₂ _∘_ refl (cong₂ _∘_
      refl (cong₂ _∘_ refl (⋆Assoc _ _ _ ∙ cong₂ _∘_ (sym (δ .N-hom _)) refl))))
    -- δ ⋆ D f ⋆ δ ⋆ D l ⋆ D T g ⋆ D μ ⋆ l     ⋆ T h ⋆ μ
    ∙ cong₂ _⋆_ (⋆Assoc _ _ _ ∙
        cong₂ _⋆_ refl (⋆Assoc _ _ _ ∙ cong₂ _⋆_ refl μ-law)) refl
    -- δ ⋆ D f ⋆ δ ⋆ D l ⋆ D T g ⋆ l * T l ⋆ μ ⋆ T h ⋆ μ
    ∙ cong₂ _∘_ refl (cong₂ _⋆_ refl (sym (⋆Assoc _ _ _) ∙
      cong₂ _∘_ refl (sym (⋆Assoc _ _ _) ∙ cong₂ _∘_ refl (l .N-hom _))))
    -- δ ⋆ D f ⋆ δ ⋆ D l ⋆ l ⋆ T D g * T l ⋆ μ ⋆ T h ⋆ μ
    ∙ cong₂ _∘_ refl (sym (⋆Assoc _ _ _) ∙ cong₂ _∘_ refl (sym (⋆Assoc _ _ _) ∙
      cong₂ _∘_ refl (⋆Assoc _ _ _ ∙ ⋆Assoc _ _ _ ∙ cong₂ _⋆_ refl
        (sym (⋆Assoc _ _ _) ∙ sym (⋆Assoc _ _ _) ∙ cong₂ _∘_
          refl ((⋆Assoc _ _ _) ∙ ⋆Assoc _ _ _ ∙ cong₂ _⋆_
            refl (sym (⋆Assoc _ _ _) ∙ sym δ-law))))))
    -- δ ⋆ D f ⋆ l ⋆ T δ ⋆ T D g * T l ⋆ μ ⋆ T h ⋆ μ
    ∙ (⋆Assoc _ _ _ ∙ cong₂ _⋆_ refl (sym (⋆Assoc _ _ _) ∙
      cong₂ _∘_ refl (sym (μ .N-hom _))))
    -- δ ⋆ D f ⋆ l ⋆ T δ ⋆ T D g ⋆ T l ⋆ T T h ⋆ μ ⋆ μ
    ∙ cong₂ _⋆_ refl (⋆Assoc _ _ _ ∙ cong₂ _⋆_ refl (λ i → assoc-μ (~ i) ⟦ _ ⟧))
    -- δ ⋆ D f ⋆ l ⋆ T δ ⋆ T D g ⋆ T l ⋆ T T h ⋆ T μ ⋆ μ
      ∙ lem0
    -- δ ⋆ D f ⋆ l ⋆ T (δ ⋆ D g ⋆ l ⋆ T h ⋆ μ) ⋆ μ
      where
        lem0 : C .Category._⋆_ (C .Category._⋆_ (D .snd .IsComonad.δ .N-ob _)
               (C .Category._⋆_ k (law .fst .N-ob _ ⋆ F-hom (T .fst)
                 (N-ob (D .snd .IsComonad.δ) _)) ⋆ F-hom (T .fst) k') ⋆
                   F-hom (T .fst) (N-ob (law .fst) _))
                   (C .Category._⋆_ (F-hom (T .fst) (F-hom (T .fst) h))
                   (F-hom (T .fst) (N-ob (T .snd .IsMonad.μ) _) ⋆
                   T .snd .IsMonad.μ .N-ob _)) ≡
                   ((δ .N-ob _ ⋆ k) ⋆ N-ob l _) ⋆ F-hom (T .fst)
                     (((δ .N-ob _ ⋆ k') ⋆ N-ob l _) ⋆
                       F-hom (T .fst) h ⋆ N-ob μ _) ⋆ N-ob μ _
        lem0 {k}{k'} = solveFunctor! C C (T .fst)
