{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Comonad.Instances.Environment where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Monad.Base
import Cubical.Categories.Monad.ExtensionSystem as MES
open import Cubical.Categories.Comonad.ExtensionSystem
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.Base
open import Cubical.Tactics.FunctorSolver.Reflection
private
  variable
    ℓ ℓ' : Level

open NatTrans

module _ {C : Category ℓ ℓ'} (Γ : Category.ob C)
         (-×Γ : ∀ c → BinProduct C (c , Γ)) where
  open Category C
  open BinProductsWithNotation -×Γ renaming (_×a to _×Γ)
  open MES.ExtensionSystemFor
  EnvEF : ExtensionSystemFor C _×Γ
  EnvEF .η = π₁
  EnvEF .bind f = f ,p π₂ -- π₁ ,p f
  EnvEF .bind-l = ×β₁ -- ×β₂ -- ×η'
  EnvEF .bind-r = sym ×ue.weak-η -- sym ×η' -- sym ×β₂
  EnvEF .bind-comp = ×ue.intro-natural
    ∙ ⟨ refl ⟩,p⟨ ×β₂ ⟩

  Env : ExtensionSystem C
  Env = _×Γ , EnvEF

module _ {C : Category ℓ ℓ'} (bp : BinProducts C) where
  open Category C
  open BinProductsNotation bp
  open Functor
  open MES.MonadMorphism

  Envs : Functor C (COMONAD C)
  Envs .F-ob Γ = Env Γ λ c → bp (c , Γ)
  Envs .F-hom γ .trans _ = π₁ ,p (π₂ ⋆ γ )
  Envs .F-hom γ .preserve-η a = ×β₁
  Envs .F-hom γ .preserve-bind a b f =
    ×ue.intro-natural _ _
    ∙ ⟨ sym ×β₁ ⟩,p⟨ ×β₂ ∙ ⟨ sym ×β₂ ⟩⋆⟨ refl ⟩ ∙ ⋆Assoc _ _ _ ⟩
    ∙ (sym $ ×ue.intro-natural _ _)
  Envs .F-id = ComonadMorphism≡ _ (funExt λ _ →
    ,p≡ (sym $ ⋆IdL _) (⋆IdR _ ∙ (sym $ ⋆IdL _)))
  Envs .F-seq f g = ComonadMorphism≡ _ (funExt λ _ →
    ,p≡
      (sym ×β₁ ∙ ⟨ refl ⟩⋆⟨ sym ×β₁ ⟩ ∙ (sym $ ⋆Assoc _ _ _)) --
      ((sym $ ⋆Assoc _ _ _) ∙ ⟨ sym ×β₂ ⟩⋆⟨ refl ⟩ ∙ ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ sym ×β₂ ⟩ ∙ (sym $ ⋆Assoc _ _ _))
      )

-- module EnvNotation {C : Category ℓ ℓ'} (bp : BinProducts C) where
--   open Category C
--   open Functor
--   open BinProductsNotation C bp

--   With : (Γ : ob) → Category _ _
--   With Γ = Kleisli C (Envs bp ⟅ Γ ⟆)

--   _^* : ∀ {Δ Γ} (γ : C [ Δ , Γ ]) → Functor (With Γ) (With Δ)
--   γ ^* = pull C (Envs bp ⟪ γ ⟫)

--   -- sometimes it's easier to prove by definition that re-use a lemma
--   id^* : ∀ {Γ} → (id {Γ}) ^* ≡ Id
--   id^* {Γ} =
--     Functor≡
--       (λ c → refl)

--       -- λ f → cong₂ _⋆_ (cong₂ _,p_ (⋆IdR _) refl ∙ sym ×η') refl ∙ ⋆IdL _

--   comp^* : ∀ {Γ Γ' Γ''} → (γ' : Hom[ Γ' , Γ'' ])(γ : Hom[ Γ , Γ' ])
--          → ((γ' ∘ γ) ^*) ≡ (γ ^*) ∘F (γ' ^*)
--   comp^* γ' γ =
--     Functor≡
--       (λ c → refl)
--       ?
--       -- (λ f →  cong₂ _⋆_ (cong₂ _,p_ (( sym (⋆Assoc _ _ _) ∙
--       --         cong₂ _∘_ refl (sym ×β₁)) ∙ ⋆Assoc _ _ _) (sym ×β₂) ∙
--       --           sym ,p-natural) refl ∙ ⋆Assoc _ _ _)
