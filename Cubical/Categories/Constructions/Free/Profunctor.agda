{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.Profunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.CoGraph
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Morphism
open import Cubical.Categories.NaturalTransformation.Base hiding (_⟦_⟧)
open import Cubical.Data.Graph.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Data.Graph.Properties
open import Cubical.Categories.Constructions.Free.General
open import Cubical.Categories.Constructions.Free.UnderlyingGraph

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓr ℓr' : Level

open Category
open Functor
open NatTrans

module FreeProfunctor (G : Graph ℓg ℓg')
                      (H : Graph ℓh ℓh')
                      (R : G .Node → H .Node → Type ℓr) where
  module FG = FreeCategory G
  module FH = FreeCategory H

  data R-type : Type (ℓ-max ℓg ℓh) where
    ↑g : G .Node → R-type
    ↑h : H .Node → R-type
  data R-generator : R-type → R-type →
                     Type (ℓ-max ℓr (ℓ-max (ℓ-max ℓg ℓg') (ℓ-max ℓh ℓh'))) where
    ↑g : ∀ {a b} → G .Edge a b → R-generator (↑g a) (↑g b)
    ↑h : ∀ {a b} → H .Edge a b → R-generator (↑h a) (↑h b)
    ↑r : ∀ {a b} → R a b → R-generator (↑g a) (↑h b)

  R-graph : Graph _ _
  R-graph .Node = R-type
  R-graph .Edge = R-generator

  module FRcat = FreeCategory R-graph

  G-i : Functor FG.FreeCat FRcat.FreeCat
  G-i =
    FG.Semantics.sem _ (record { _$g_ = ↑g ; _<$g>_ = λ x → FRcat.↑ (↑g x) })

  H-i : Functor FH.FreeCat FRcat.FreeCat
  H-i =
    FH.Semantics.sem _ (record { _$g_ = ↑h ; _<$g>_ = λ x → FRcat.↑ (↑h x) })

  FR : FG.FreeCat o-[ _ ]-* FH.FreeCat
  FR = HomFunctor FRcat.FreeCat ∘F ((G-i ^opF) ×F H-i)

  ηR : ∀ {a b} → R a b → ⟨ FR ⟅ a , b ⟆ ⟩
  ηR r = FRcat.↑ (↑r r)

  module Semantics {𝓒 : Category ℓc ℓc'}
                   {𝓓 : Category ℓd ℓd'} {𝓡 : 𝓒 o-[ ℓr' ]-* 𝓓}
                   (ıG : Interp G 𝓒)
                   (ıH : Interp H 𝓓)
                   (ıR : ∀ {A B} → R A B → ⟨ 𝓡 ⟅ ıG $g A , ıH $g B ⟆ ⟩)
                   where
    sem𝓒 = FG.Semantics.sem 𝓒 ıG
    sem𝓓 = FH.Semantics.sem 𝓓 ıH

    open ProfHom
    CGR = CoGraph {C = 𝓒} {D = 𝓓} 𝓡
    sem𝓡CoGraph : Functor FRcat.FreeCat CGR
    sem𝓡CoGraph =
      FRcat.Semantics.sem CGR
        (record { _$g_ = sem𝓡-ob ; _<$g>_ = sem𝓡-gen }) where
      sem𝓡-ob : R-type → CGR .ob
      sem𝓡-ob (↑g x) = inl (sem𝓒 ⟅ x ⟆ )
      sem𝓡-ob (↑h x) = inr (sem𝓓 ⟅ x ⟆ )

      sem𝓡-gen : ∀ {x y} → R-generator x y → CGR [ sem𝓡-ob x , sem𝓡-ob y ]
      sem𝓡-gen (↑g x) = ↑o (ıG <$g> x)
      sem𝓡-gen (↑r x) = ↑p (ıR x)
      sem𝓡-gen (↑h x) = ↑* (ıH <$g> x)

    sem𝓡CG-G : sem𝓡CoGraph ∘F G-i ≡ (↑oF 𝓡 ∘F sem𝓒)
    sem𝓡CG-G = FG.induction _ _ (GrHom≡ (λ v → refl) (λ e → refl))

    sem𝓡CG-H : sem𝓡CoGraph ∘F H-i ≡ (↑*F 𝓡 ∘F sem𝓓)
    sem𝓡CG-H = FH.induction _ _ (GrHom≡ (λ v → refl) (λ e → refl))

    sem𝓡 : ProfHom FR sem𝓒 sem𝓓 𝓡
    sem𝓡 .R-hom b c x = ↑p-r 𝓡 (sem𝓡CoGraph ⟪ x ⟫)
    sem𝓡 .R-nat b' b c c' f p g =
      cong (↑p-r 𝓡) ((λ i → sem𝓡CoGraph .F-seq (p ∘⟨ FRcat.FreeCat ⟩
                        G-i ⟪ f ⟫) (H-i ⟪ g ⟫) i)
                    ∙ (λ i → (sem𝓡CoGraph ⟪ H-i ⟪ g ⟫ ⟫) ∘⟨ CGR ⟩
                         sem𝓡CoGraph .F-seq (G-i ⟪ f ⟫) p i)
                    ∙ λ i → sem𝓡CG-H i ⟪ g ⟫ ∘⟨ CGR ⟩
                        sem𝓡CoGraph ⟪ p ⟫ ∘⟨ CGR ⟩ sem𝓡CG-G i ⟪ f ⟫)
      ∙ ↑pH-r 𝓡 .R-nat _ _ _ _ (sem𝓒 ⟪ f ⟫) (sem𝓡CoGraph ⟪ p ⟫) (sem𝓓 ⟪ g ⟫)
