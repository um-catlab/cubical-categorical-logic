{-

  Simple categories with families are one approach to modeling the
  judgmental structure of simply typed lambda calculus. TODO: citation

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.WithFamilies.Simple.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions

open Category
open NatTrans

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level
SCwF : (ℓC ℓC' ℓT ℓT' : Level) → Type _
SCwF ℓC ℓC' ℓT ℓT' =
  Σ[ C ∈ Category ℓC ℓC' ]
  Σ[ Ty ∈ Type ℓT ]
  Σ[ Tm ∈ (Ty → Presheaf C ℓT') ]
  Terminal C ×
  (∀ (Γ : C .ob) (A : Ty) → UniversalElement C ((C [-, Γ ]) ×𝓟 Tm A))


PreMorphism : SCwF ℓC ℓC' ℓT ℓT' → SCwF ℓD ℓD' ℓS ℓS' → Type _
PreMorphism (C , CTy , CTm , Cterm , Ccomp) (D , DTy , DTm , Dterm , Dcomp) =
  Σ[ F ∈ Functor C D ]
  Σ[ F-Ty ∈ (CTy → DTy) ]
  (∀ (A : CTy) → PshHomⱽ (CTm A) (DTm (F-Ty A) ∘F (F ^opF)))
  
-- Two options here:
-- 1. Strict: preserve the specified terminal/comprehension/projections up to Path
-- 2. Weak: image of the terminal object is terminal, image of the comprehension cone is universal
-- strict morphisms are always weak , the inverse follows if the SCwF is univalent
open UniversalElement
WkMorphism : SCwF ℓC ℓC' ℓT ℓT' → SCwF ℓD ℓD' ℓS ℓS' → Type _
WkMorphism (C , CTy , CTm , Cterm , Ccomp) (D , DTy , DTm , Dterm , Dcomp) =
  Σ[ F ∈ Functor C D ]
  Σ[ F-Ty ∈ (CTy → DTy) ]
  Σ[ F-Tm ∈ (∀ (A : CTy) → PshHom F (CTm A) (DTm (F-Ty A))) ]
  isTerminal D (F ⟅ Cterm .fst ⟆)
  × (∀ (Γ : C .ob) (A : CTy)
  → isUniversal D (((D [-, (F ⟅ Γ ⟆ ) ]) ×𝓟 DTm (F-Ty A)))
      (F ⟅ Ccomp Γ A .vertex ⟆)
      ((F ⟪ Ccomp Γ A .element .fst ⟫) , F-Tm A .N-ob _ (lift $ Ccomp Γ A .element .snd) .lower)) 

StrictMorphism : SCwF ℓC ℓC' ℓT ℓT' → SCwF ℓD ℓD' ℓS ℓS' → Type _
StrictMorphism (C , CTy , CTm , Cterm , Ccomp) (D , DTy , DTm , Dterm , Dcomp) =
  Σ[ F ∈ Functor C D ]
  Σ[ F-Ty ∈ (CTy → DTy) ]
  Σ[ F-Tm ∈ (∀ (A : CTy) → PshHom F (CTm A) (DTm (F-Ty A))) ]
  (F ⟅ Cterm .fst ⟆ ≡ Dterm .fst)
  × (∀ (Γ : C .ob) (A : CTy) →
    Path (Σ[ FΓ×FA ∈ D .ob ] (D [ FΓ×FA , F ⟅ Γ ⟆ ]) × ⟨ DTm (F-Ty A) ⟅ FΓ×FA ⟆ ⟩)
      (F ⟅ Ccomp Γ A .vertex ⟆ , F ⟪ Ccomp Γ A .element .fst ⟫ , F-Tm A .N-ob (Ccomp Γ A .vertex) (lift (Ccomp Γ A .element .snd)) .lower)
      (Dcomp (F ⟅ Γ ⟆) (F-Ty A) .vertex , Dcomp (F ⟅ Γ ⟆) (F-Ty A) .element .fst , Dcomp (F ⟅ Γ ⟆) (F-Ty A) .element .snd)
      )
