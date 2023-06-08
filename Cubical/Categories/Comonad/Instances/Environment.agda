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
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.Base
open import Cubical.Tactics.FunctorSolver.Reflection
private
  variable
    ℓ ℓ' : Level

open BinProduct
open NatTrans

module _ {C : Category ℓ ℓ'} (Γ : Category.ob C)
         (Γ×- : ∀ c → BinProduct C Γ c) where
  open Category C
  open ProdsWithNotation C Γ×- renaming (a×_ to Γ×_)
  open MES.ExtensionSystemFor
  EnvEF : ExtensionSystemFor C (Γ×_)
  EnvEF .η = π₂
  EnvEF .bind f = π₁ ,p f
  EnvEF .bind-l = ×β₂ -- ×η'
  EnvEF .bind-r = sym ×η' -- sym ×β₂
  EnvEF .bind-comp = ,p-natural ∙ cong₂ _,p_ ×β₁ refl

  Env : ExtensionSystem C
  Env = Γ×_ , EnvEF

module _ {C : Category ℓ ℓ'} (bp : BinProducts C) where
  open Category C
  open Notation C bp
  open Functor
  open MES.MonadMorphism

  Envs : Functor C (COMONAD C)
  Envs .F-ob Γ = Env Γ (bp Γ)
  Envs .F-hom γ .trans _ = (γ ∘⟨ C ⟩ π₁) ,p π₂ -- γ ∘⟨ C ⟩ π₁ ,p π₂
  Envs .F-hom γ .preserve-η a = ×β₂
  Envs .F-hom γ .preserve-bind a b f =
    ,p-natural
    ∙ cong₂ _,p_ (×β₁ ∙ cong₂ (seq' C) (sym ×β₁) refl ∙ ⋆Assoc _ _ _)
                 (sym ×β₂)
    ∙ sym ,p-natural
  Envs .F-id = ComonadMorphism≡ C (funExt λ x →
    cong₂ _,p_ (⋆IdR _ ∙ sym (⋆IdL _)) (sym (⋆IdL _)) ∙ sym ×η)
  Envs .F-seq f g = ComonadMorphism≡ C (funExt λ x →
    cong₂ _,p_ (sym (⋆Assoc _ _ _) ∙
    cong₂ _⋆_ (sym ×β₁) refl ∙ ⋆Assoc _ _ _) (sym ×β₂) ∙ sym ,p-natural)
module EnvNotation {C : Category ℓ ℓ'} (bp : BinProducts C) where
  open Category C
  open Functor
  open Notation C bp

  With : (Γ : ob) → Category _ _
  With Γ = Kleisli C (Envs bp ⟅ Γ ⟆)

  _^* : ∀ {Δ Γ} (γ : C [ Δ , Γ ]) → Functor (With Γ) (With Δ)
  γ ^* = pull C (Envs bp ⟪ γ ⟫)

  -- sometimes it's easier to prove by definition that re-use a lemma
  id^* : ∀ {Γ} → (id {Γ}) ^* ≡ Id
  id^* {Γ} =
    Functor≡
      (λ c → refl)
      λ f → cong₂ _⋆_ (cong₂ _,p_ (⋆IdR _) refl ∙ sym ×η') refl ∙ ⋆IdL _

  comp^* : ∀ {Γ Γ' Γ''} → (γ' : Hom[ Γ' , Γ'' ])(γ : Hom[ Γ , Γ' ])
         → ((γ' ∘ γ) ^*) ≡ (γ ^*) ∘F (γ' ^*)
  comp^* γ' γ =
    Functor≡
      (λ c → refl)
      (λ f →  cong₂ _⋆_ (cong₂ _,p_ (( sym (⋆Assoc _ _ _) ∙
              cong₂ _∘_ refl (sym ×β₁)) ∙ ⋆Assoc _ _ _) (sym ×β₂) ∙
                sym ,p-natural) refl ∙ ⋆Assoc _ _ _)
