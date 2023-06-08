{-# OPTIONS --safe #-}
module Cubical.Categories.DistributiveLaw.ComonadOverMonad.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Comonad.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

open NatTrans
-- open isMonad
-- Here we model the comonad as a monad on the opposite
-- category. Worth refactoring at some point

record IsDistributiveLaw {C : Category ℓ ℓ'} (D : Comonad C) (T : Monad C)
       (l : NatTrans (D .fst ∘F T .fst) (T .fst ∘F D .fst)) :
         Type (ℓ-max ℓ ℓ') where
  Df : Functor C C
  Df = D .fst
  open IsComonad (D .snd)
  Tf = T .fst
  open IsMonad (T .snd)
  open Category C

  field
    -- This way avoids PathPs
    ε-law : ∀ {c} → ((Tf ∘ʳ ε) ∘ᵛ l) .N-ob c ≡ (ε ∘ˡ Tf) .N-ob c
    δ-law : ∀ {c} →
      -- T δ ∘ l
      -- ≡ l ∘ D l ∘ δ
      ((Tf ∘ʳ δ) ∘ᵛ l) .N-ob c
      ≡ (l ∘ˡ Df) ⟦ c ⟧ ∘ ((Df ∘ʳ l) ⟦ c ⟧ ∘ (δ ∘ˡ Tf) ⟦ c ⟧)
    η-law : ∀ {c} → (l ∘ᵛ (Df ∘ʳ η)) .N-ob c ≡ (η ∘ˡ Df) .N-ob c
    μ-law : ∀ {c} →
      -- l ∘ D μ ≡ μ ∘ T l ∘ l
      (l ∘ᵛ (Df ∘ʳ μ)) .N-ob c
      ≡ (μ ∘ˡ Df) ⟦ c ⟧ ∘ ((Tf ∘ʳ l) ⟦ c ⟧ ∘ (l ∘ˡ Tf) ⟦ c ⟧)

open IsDistributiveLaw

DistributiveLaw : ∀ {C : Category ℓ ℓ'} (D : Comonad C) (T : Monad C) → Type _
DistributiveLaw D T = Σ _ (IsDistributiveLaw D T)

-- This is the level of generality I need but in general you can have
-- a monad morphism as well, but using it more specifically has extra
-- id's in the definition.
module _ {C : Category ℓ ℓ'}
         {D : Comonad C}
         {T : Monad C}
         {D' : Comonad C}
         (law : DistributiveLaw D T) (law' : DistributiveLaw D' T) where
  -- D' T -- l' --> T D'
  -- |              |
  -- ϕ T            T ϕ
  -- |              |
  ---D T  -- l  --> T D
  -- note the inversion here
  isComonadMorphism : ComonadHom D' D → Type _
  isComonadMorphism ϕ =
    law .fst ∘ᵛ (ϕ .fst ∘ˡ T .fst) ≡ (T .fst ∘ʳ ϕ .fst) ∘ᵛ law' .fst

  ComonadMorphism : Type _
  ComonadMorphism = Σ _ isComonadMorphism

module _ {C : Category ℓ ℓ'} where
  open Category C
  open Functor

  idCMM : ∀  {D : Comonad C} {T : Monad C} (law : DistributiveLaw D T) →
    ComonadMorphism law law
  idCMM {D = D} law .fst = idCoHom D
  idCMM {D = D}{T = T} law .snd =
    makeNatTransPath
      (funExt
        (λ x → ⋆IdL _ ∙ sym (⋆IdR _) ∙ cong₂ _⋆_ refl (sym (T .fst .F-id))))

  module _ {D D' D'' : Comonad C}
           {T : Monad C}
           {law : DistributiveLaw D T}
           {law' : DistributiveLaw D' T} {law'' : DistributiveLaw D'' T} where
    -- note the inversion
    compCMM : ComonadMorphism law' law'' →
              ComonadMorphism law law' → ComonadMorphism law law''
    compCMM ϕ ϕ' .fst = compCoHom (ϕ' .fst) (ϕ .fst)
    compCMM ϕ ϕ' .snd =
      makeNatTransPath
        (funExt (λ x → ⋆Assoc _ _ _ ∙
                       cong₂ _⋆_ refl (λ i → ϕ' .snd i ⟦ _ ⟧) ∙
                       sym (⋆Assoc _ _ _) ∙
                       cong₂ _∘_ refl ((λ i → ϕ .snd i ⟦ _ ⟧)) ∙
                       (⋆Assoc _ _ _) ∙
                       cong₂ _⋆_ refl (sym (T .fst .F-seq _ _)) ))
