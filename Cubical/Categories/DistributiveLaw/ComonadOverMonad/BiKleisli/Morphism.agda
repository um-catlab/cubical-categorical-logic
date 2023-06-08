{-# OPTIONS --safe #-}
module Cubical.Categories.DistributiveLaw.ComonadOverMonad.BiKleisli.Morphism
  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Comonad.Base

open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.Base
open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.BiKleisli.Base
open import Cubical.Tactics.FunctorSolver.Reflection
open import Cubical.Tactics.CategorySolver.Reflection
private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} {D : Comonad C} {T : Monad C}{D' : Comonad C}
         {law : DistributiveLaw D T}
         {law' : DistributiveLaw D' T}
         (ϕ : ComonadMorphism law law')
         where
  open Category C
  open Functor
  open NatTrans
  open IsComonad
  open IsComonadHom
  private
    variable
      a b c : ob
      h k : Hom[ a , b ]
  change-of-comonad : Functor (BiKleisli D T law) (BiKleisli D' T law')
  change-of-comonad .F-ob x = x
  change-of-comonad .F-hom {x} {y} f = f ∘ ϕ .fst .fst ⟦ x ⟧
  change-of-comonad .F-id =
    sym (⋆Assoc _ _ _) ∙ cong₂ _∘_ refl (λ i → ϕ .fst .snd .V-ε i ⟦ _ ⟧)
  change-of-comonad .F-seq {x}{y}{z} f g =
    -- ϕ ⋆ δ ⋆ D f ⋆ l   ⋆ T g ⋆ μ
    (lem0 ∙ cong₂ _∘_ refl (λ i → ϕ .fst .snd .V-δ i ⟦ _ ⟧))
    -- δ' ⋆ D' ϕ ⋆ ϕ ⋆ D f ⋆ l   ⋆ T g ⋆ μ
    ∙ (lem1 ∙ cong₂ _⋆_ refl (cong₂ _∘_ refl (sym (ϕ .fst .fst .N-hom f))))
    -- δ' ⋆ D' ϕ ⋆ D' f ⋆ ϕ ⋆ l   ⋆ T g ⋆ μ
    ∙ (lem2 ∙ cong₂ _⋆_ refl (cong₂ _∘_ refl λ i → ϕ .snd i ⟦ _ ⟧))
    -- δ' ⋆ D' ϕ ⋆ D' f ⋆ l' ⋆ T ϕ ⋆ T g ⋆ μ
    ∙ lem3
    ∙ lem4
    -- ≡ δ' ⋆ D' (ϕ ⋆ f) ⋆ l' ⋆ T (ϕ ⋆ g) ⋆ μ
    where
      lem0 : N-ob (ϕ .fst .fst) x ⋆ ((δ (D .snd) .N-ob x ⋆
        F-hom (D .fst) f) ⋆ N-ob (fst law) y) ⋆
        F-hom (T .fst) g ⋆ N-ob (IsMonad.μ (T .snd)) z
           ≡ ((N-ob (ϕ .fst .fst) x ⋆ δ (D .snd) .N-ob x) ⋆
             (((F-hom (D .fst) f) ⋆ N-ob (fst law) y) ⋆
             F-hom (T .fst) g ⋆ N-ob (IsMonad.μ (T .snd)) z))
      lem0 = solveCat! C

      lem1 : (snd D' .δ .N-ob x ⋆ F-hom (fst D') (N-ob (ϕ .fst .fst) x) ⋆
             N-ob (ϕ .fst .fst) (F-ob (D .fst) x)) ⋆
             C .Category._⋆_ (C .Category._⋆_ (F-hom (D .fst) f)
               (N-ob (fst law) y))
               (C .Category._⋆_ (F-hom (T .fst) g)
                 (N-ob (IsMonad.μ (T .snd)) z))
           ≡ (snd D' .δ .N-ob x ⋆ F-hom (fst D')
             (N-ob (ϕ .fst .fst) x)) ⋆ (N-ob (ϕ .fst .fst) (F-ob (D .fst) x) ⋆
            (F-hom (D .fst) f)) ⋆ ((N-ob (fst law) y) ⋆ (F-hom (T .fst) g) ⋆
              (N-ob (IsMonad.μ (T .snd)) z))

      lem1 = solveCat! C

      lem2 : C .Category._⋆_ (C .Category._⋆_
        (snd D' .δ .N-ob x)
        (F-hom (fst D') (N-ob (ϕ .fst .fst) x)))
        ((fst D' .F-hom f ⋆ ϕ .fst .fst .N-ob (F-ob (T .fst) y)) ⋆
          C .Category._⋆_ (N-ob (fst law) y) (C .Category._⋆_
            (F-hom (T .fst) g) (N-ob (IsMonad.μ (T .snd)) z)))
           ≡ C .Category._⋆_ (C .Category._⋆_ (snd D' .δ .N-ob x)
             (F-hom (fst D') (N-ob (ϕ .fst .fst) x)))
             (fst D' .F-hom f) ⋆
             (ϕ .fst .fst .N-ob (F-ob (T .fst) y) ⋆ (N-ob (fst law) y)) ⋆
             (C .Category._⋆_ (F-hom (T .fst) g) (N-ob (IsMonad.μ (T .snd)) z))
      lem2 = solveCat! C
      --p
      lem3 : C .Category._⋆_ (C .Category._⋆_
           (C .Category._⋆_ (snd D' .δ .N-ob x) (F-hom (fst D')
             (N-ob (ϕ .fst .fst) x)))
           (fst D' .F-hom f)) ((law' .fst .N-ob y ⋆ h) ⋆
             C .Category._⋆_ k (N-ob (IsMonad.μ (T .snd)) z))
           ≡ C .Category._⋆_ (C .Category._⋆_ (snd D' .δ .N-ob x)
             ((F-hom (fst D') ((N-ob (ϕ .fst .fst) x) ⋆ f))))
               ((law' .fst .N-ob y ⋆ h) ⋆ C .Category._⋆_
                 k (N-ob (IsMonad.μ (T .snd)) z))
      lem3 = solveFunctor! C C (D' .fst)

      lem4 : C .Category._⋆_ (C .Category._⋆_ (snd D' .δ .N-ob x) h)
             (C .Category._⋆_ (C .Category._⋆_ (law' .fst .N-ob y)
               (F-hom (T .fst) (N-ob (ϕ .fst .fst) y)))
               (C .Category._⋆_ (F-hom (T .fst) g)
                 (N-ob (IsMonad.μ (T .snd)) z)))
           ≡ ((δ (D' .snd) .N-ob x ⋆ h) ⋆ N-ob (fst law') y) ⋆
                 F-hom (T .fst) (N-ob (ϕ .fst .fst) y ⋆ g) ⋆
                 N-ob (IsMonad.μ (T .snd)) z
      lem4 = solveFunctor! C C (T .fst)
