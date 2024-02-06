{-# OPTIONS --safe #-}
module Cubical.Tactics.AltFunctorSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Data.Sum as Sum

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Power
open import Cubical.Categories.Functor renaming (Id to IdF)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.UnderlyingGraph

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Preorder hiding (Section; reindex)
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Constructions.Free.Category.Quiver as FreeCat
open import Cubical.Categories.Constructions.Free.Functor.AltPresented

private
  variable
    ℓc ℓc' ℓd ℓd' ℓb ℓb' : Level
open Category
open Functor
open Section
open Interpᴰ

module Eval (𝓒 : Category ℓc ℓc') (𝓓 : Category ℓd ℓd')  (𝓕 : Functor 𝓒 𝓓) where
  module Self = CoUnit 𝓕
  open Self

  Free𝓒 = FreeCat (CatQuiver 𝓒)
  η𝓒 = FreeCat.η (CatQuiver 𝓒)
  Free𝓓 = Self.HCat
  η𝓓 = Self.ηHCat
  Free𝓕 = Self.FreeFunctor

  ε𝓒 : Section (weaken Free𝓒 𝓒)
  ε𝓒 = FreeCat.elim (CatQuiver 𝓒) ı where
    ı : Interpᴰ (𝓒 .ob , CatQuiver 𝓒 .snd) (weaken Free𝓒 𝓒)
    ı .I-ob = λ c → c
    ı .I-hom e = e .snd .snd
  open FreeFunctor.HInterpᴰ

  sem : Section (weaken Free𝓓 𝓓)
  sem = Self.elim ε𝓒 (weakenF 𝓕) ı where
    ı : HInterpᴰ ε𝓒 (weakenF 𝓕)
    ı .I-obH A = A
    ı .I-homH (inl x , inl x₁ , e) = e
    ı .I-homH (inl x , inr x₁ , e) = e
    ı .I-homH (inr x , inl x₁ , e) = e
    ı .I-homH (inr x , inr x₁ , e) = e

  -- Normalization is by interpretation into the presheaf category
  𝓟F𝓓 = PowerCategory (Free𝓓 .ob) (SET (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd'))
  Y : Section (weaken Free𝓓 𝓟F𝓓)
  Y = Iso.inv (SectionToWkIsoFunctor _ _) (PseudoYoneda {C = Free𝓓})

  selfFree𝓒 : Section (weaken Free𝓒 𝓟F𝓓)
  selfFree𝓒 = FreeCat.elim (CatQuiver 𝓒) ı where
    ı : Interpᴰ (𝓒 .ob , CatQuiver 𝓒 .snd) _
    ı .I-ob = (PseudoYoneda {C = Free𝓓} ∘F Self.FreeFunctor) .F-ob
    ı .I-hom e =
      (PseudoYoneda {C = Free𝓓} ∘F Self.FreeFunctor) .F-hom (η𝓒 .I-hom e)

  Normalize : Section (weaken Free𝓓 𝓟F𝓓)
  Normalize = Self.elim selfFree𝓒 (weakenF IdF) ı where
    ı : HInterpᴰ selfFree𝓒 _
    ı .I-obH A = Y .F-ob (inr A)
    ı .I-homH (inl A , inl B , e) = Y .F-hom (η𝓓 .I-hom (inr (_ , _ , e)))
    ı .I-homH (inl A , inr B , e) = Y .F-hom (η𝓓 .I-hom (inr (_ , _ , e)))
    ı .I-homH (inr A , inl B , e) = Y .F-hom (η𝓓 .I-hom (inr (_ , _ , e)))
    ı .I-homH (inr A , inr B , e) = Y .F-hom (η𝓓 .I-hom (inr (_ , _ , e)))

  -- Normalization is equivalent to Yoneda because they agree on generators
  Normalize≡Y : Normalize ≡ Y
  Normalize≡Y = SecPathSectionToSectionPath
                (weaken Free𝓓 𝓟F𝓓)
                (Iso.inv (PreorderSectionIsoCatSection _ _) N≡Y) where
    N≡Yᴰ = (Preorderᴰ→Catᴰ (SecPath (weaken Free𝓓 𝓟F𝓓) Normalize Y))

    agree-on-Free𝓒 : Section (reindex N≡Yᴰ Self.FreeFunctor)
    agree-on-Free𝓒 = FreeCat.elim (CatQuiver 𝓒) ı where
      ı : Interpᴰ (𝓒 .ob , CatQuiver 𝓒 .snd) _
      ı .I-ob c = refl
      ı .I-hom e = refl

    N≡Y : Section N≡Yᴰ
    N≡Y = Self.elim agree-on-Free𝓒 (reindexΠ _ _) ı where
      ı : HInterpᴰ agree-on-Free𝓒 _
      ı .I-obH A = refl
      ı .I-homH (inl A , inl B , e) = refl
      ı .I-homH (inl A , inr B , e) = refl
      ı .I-homH (inr A , inl B , e) = refl
      ı .I-homH (inr A , inr B , e) = refl

  solve : ∀ {A B}
        → (e e' : Free𝓓 [ A , B ])
        → (Normalize .F-hom e ≡ Normalize .F-hom e')
        → (sem .F-hom e ≡ sem .F-hom e')
  solve e e' p =
    cong (sem .F-hom)
    -- suffices to show e ≡ e'
    (isFaithfulPseudoYoneda {C = Free𝓓} _ _ e e'
    -- suffices to show Y e ≡ Y e'
    (transport (λ i → Path _
                           (Normalize≡Y i .F-hom e)
                           ((Normalize≡Y i .F-hom e')))
               p))

  readBack : ∀ {A B} → 𝓟F𝓓 [ Normalize .F-ob A , Normalize .F-ob B ]
                     → Free𝓓 [ A , B ]
  readBack {inl x} {inl x₁} f = f _ (Free𝓓 .id)
  readBack {inl x} {inr x₁} f = f _ (Free𝓓 .id)
  readBack {inr x} {inl x₁} f = f _ (Free𝓓 .id)
  readBack {inr x} {inr x₁} f = f _ (Free𝓓 .id)

  -- TODO: prove this
  -- normalise : ∀ {A B } → ∀ (e : Free𝓓 [ A , B ]) → singl e
  -- normalise e = readBack (Normalize .F-hom e) ,
  --   {!!} ∙ cong readBack (λ i → {!Normalize≡Y (~ i) .F-hom e!})

  -- nf : ∀ {A B} → (e : Free𝓓 [ A , B ])
  --    → sem .F-hom e ≡ sem .F-hom (normalise e .fst)
  -- nf e = cong (sem .F-hom) (normalise e .snd)

  private
    module _ (A A' A'' : 𝓒 .ob) (B B' B'' : 𝓓 .ob)
             (f : 𝓓 [ B , B' ])
             (g : 𝓓 [ 𝓕 ⟅ A ⟆ , B ])


             (h : 𝓒 [ A' , A ])
             (k : 𝓒 [ A'' , A' ])
             where
      fgen = (ηHCat .I-hom (inr ((inr B) , inr B' , f)))
      ggen = (ηHCat .I-hom (inr ((inl A) , inr B , g)))
      hgen = η𝓒 .I-hom (A' , A , h)
      kgen = η𝓒 .I-hom (A'' , A' , k)

      tst' : 𝓓 .id ≡ 𝓓 .id ⋆⟨ 𝓓 ⟩ 𝓓 .id
      tst' = solve (Free𝓓 .id) (Free𝓓 .id {x = inr B} ⋆⟨ Free𝓓 ⟩ Free𝓓 .id) refl

      tst2 : g ≡ ((𝓓 .id ⋆⟨ 𝓓 ⟩ g) ⋆⟨ 𝓓 ⟩ 𝓓 .id)
      tst2 = solve ggen ((Free𝓓 .id ⋆⟨ Free𝓓 ⟩ ggen) ⋆⟨ Free𝓓 ⟩ Free𝓓 .id) refl

      tst : 𝓕 ⟪ 𝓒 .id ⟫ ≡ 𝓓 .id
      tst = solve (Self.FreeFunctor ⟪ Free𝓒 .id {A} ⟫) (Free𝓓 .id) refl

      tst'' : 𝓕 ⟪ k ⟫ ⋆⟨ 𝓓 ⟩ 𝓕 ⟪ h ⟫ ≡ 𝓕 ⟪ k ⋆⟨ 𝓒 ⟩ h ⟫
      tst'' = solve
        (Self.FreeFunctor ⟪ kgen ⟫ ⋆⟨ Free𝓓 ⟩ Self.FreeFunctor ⟪ hgen ⟫)
        (Self.FreeFunctor ⟪ kgen ⋆⟨ Free𝓒 ⟩ hgen ⟫)
        refl

solve = Eval.solve
