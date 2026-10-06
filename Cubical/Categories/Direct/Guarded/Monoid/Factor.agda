{-# OPTIONS --lossy-unification #-}
open import Cubical.Categories.Direct.Instances.Monoid using (GradedMonoid)

module Cubical.Categories.Direct.Guarded.Monoid.Factor (GM : GradedMonoid) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (suc ; +-comm)
open import Cubical.Data.Nat.Order.Recursive using (_<_ ; isProp≤ ; ≤-trans ; k≤k+n ; n≤k+n)
open import Cubical.Algebra.Monoid.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Direct.Instances.Monoid using (Factor ; factorDirect)
open import Cubical.Categories.Direct.Guarded.Monoid GM
  using (Fam ; _⊗_ ; NonNullable ; pos→< ; degSplit)
open import Cubical.Categories.Direct.Guarded.Family (factorDirect GM)
  using (FamStrengthˡʳ ; strengthˡʳ→LC ; FamStrengthˡ ; strengthˡ→LC ; FamStrengthʳ ; strengthʳ→LC)
open import Cubical.Categories.Direct.Guarded.Presheaf (factorDirect GM) using (pshGuarded)
open import Cubical.Categories.Enriched.Enrichment.Instances.Family.Limits (Factor GM) ℓ-zero
  using (famEnrichment)
open import Cubical.Categories.Enriched.Enrichment.Instances.FullSubcategory
  using (FullSubcategoryEnrichment)
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive.Bifunctor pshGuarded
  using (isLocallyContractiveˡʳ ; isLocallyContractiveˡ ; isLocallyContractiveʳ)

open Functor

private
  M = GM .fst
  deg = GM .snd .fst
  open MonoidStr (M .snd)

module _ (P₁ P₂ : Category.ob Fam → Type) where
  ⊗F : Functor (FullSubcategory Fam P₁ ×C FullSubcategory Fam P₂) Fam
  ⊗F .F-ob ((X , _) , (Y , _)) = X ⊗ Y
  ⊗F .F-hom (f , g) _ (u , v , s , a , b) = u , v , s , f (tt , u) a , g (tt , v) b
  ⊗F .F-id = refl
  ⊗F .F-seq f g = refl

private
  left : ∀ {u v w} → u · v ≡ w → Factor GM [ (tt , u) , (tt , w) ]
  left {u} {v} s = (ε , v) , cong (_· v) (·IdL u) ∙ s

  right : ∀ {u v w} → u · v ≡ w → Factor GM [ (tt , v) , (tt , w) ]
  right {u} {v} s = (u , ε) , ·IdR (u · v) ∙ s

  ltL : ∀ {u v w} → u · v ≡ w → 0 < deg v → deg u < deg w
  ltL {u} {v} {w} s = pos→< (deg v) (deg u) (deg w) (+-comm (deg v) (deg u) ∙ degSplit s)

  ltR : ∀ {u v w} → u · v ≡ w → 0 < deg u → deg v < deg w
  ltR {u} {v} {w} s = pos→< (deg u) (deg v) (deg w) (degSplit s)

  ⊤ : Category.ob Fam → Type
  ⊤ _ = Unit

⊗-strengthˡʳ : FamStrengthˡʳ (⊗F NonNullable NonNullable)
⊗-strengthˡʳ .FamStrengthˡʳ.st {X} {X'} {Y} {Y'} _ e d (u , v , s , a , b) =
  u , v , s , e (tt , u) (left s) (ltL s (Y .snd v b)) a , d (tt , v) (right s) (ltR s (X .snd u a)) b
⊗-strengthˡʳ .FamStrengthˡʳ.st-seq {X} {X'} {X''} {Y} {Y'} {Y''} (_ , w) e e' d d' (u , v , s , a , b) i =
  u , v , s
  , e' (tt , u) (left s) (isProp≤ {suc (deg u)} {deg w} (ltL s (Y .snd v b))
        (ltL s (Y' .snd v (d (tt , v) (right s) (ltR s (X .snd u a)) b))) i)
      (e (tt , u) (left s) (ltL s (Y .snd v b)) a)
  , d' (tt , v) (right s) (isProp≤ {suc (deg v)} {deg w} (ltR s (X .snd u a))
        (ltR s (X' .snd u (e (tt , u) (left s) (ltL s (Y .snd v b)) a))) i)
      (d (tt , v) (right s) (ltR s (X .snd u a)) b)
⊗-strengthˡʳ .FamStrengthˡʳ.st-hom f g _ = refl

⊗-strengthˡ : FamStrengthˡ (⊗F ⊤ NonNullable)
⊗-strengthˡ .FamStrengthˡ.st {X} {X'} {Y} {Y'} _ e d (u , v , s , a , b) =
  u , v , s , e (tt , u) (left s) (ltL s (Y .snd v b)) a , d (tt , v) (right s) b
⊗-strengthˡ .FamStrengthˡ.st-seq {X} {X'} {X''} {Y} {Y'} {Y''} (_ , w) e e' d d' (u , v , s , a , b) i =
  u , v , s
  , e' (tt , u) (left s) (isProp≤ {suc (deg u)} {deg w} (ltL s (Y .snd v b))
        (ltL s (Y' .snd v (d (tt , v) (right s) b))) i)
      (e (tt , u) (left s) (ltL s (Y .snd v b)) a)
  , d' (tt , v) (right s) (d (tt , v) (right s) b)
⊗-strengthˡ .FamStrengthˡ.st-hom f g _ = refl

⊗-strengthʳ : FamStrengthʳ (⊗F NonNullable ⊤)
⊗-strengthʳ .FamStrengthʳ.st {X} {X'} {Y} {Y'} _ e d (u , v , s , a , b) =
  u , v , s , e (tt , u) (left s) a , d (tt , v) (right s) (ltR s (X .snd u a)) b
⊗-strengthʳ .FamStrengthʳ.st-seq {X} {X'} {X''} {Y} {Y'} {Y''} (_ , w) e e' d d' (u , v , s , a , b) i =
  u , v , s
  , e' (tt , u) (left s) (e (tt , u) (left s) a)
  , d' (tt , v) (right s) (isProp≤ {suc (deg v)} {deg w} (ltR s (X .snd u a))
        (ltR s (X' .snd u (e (tt , u) (left s) a))) i)
      (d (tt , v) (right s) (ltR s (X .snd u a)) b)
⊗-strengthʳ .FamStrengthʳ.st-hom f g _ = refl

⊗-LCˡʳ : isLocallyContractiveˡʳ (⊗F NonNullable NonNullable)
⊗-LCˡʳ = strengthˡʳ→LC ⊗-strengthˡʳ

⊗-LCˡ : isLocallyContractiveˡ (⊗F ⊤ NonNullable)
⊗-LCˡ = strengthˡ→LC ⊗-strengthˡ

⊗-LCʳ : isLocallyContractiveʳ (⊗F NonNullable ⊤)
⊗-LCʳ = strengthʳ→LC ⊗-strengthʳ
