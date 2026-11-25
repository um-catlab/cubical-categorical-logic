{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianClosedCategory.NbE.Neutral where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Base
open import Cubical.Categories.Displayed.Instances.Terminal.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Base

open import Gluing.CartesianClosedCategory.Renamings
open import Gluing.CartesianClosedCategory.NormalForms
open import Gluing.CartesianClosedCategory.NbE.Base

private
  variable ℓQ ℓQ' : Level

open Functor

module NePresheaf (Q : ×⇒Quiver ℓQ ℓQ') where
  private
    ℓ = ℓ-max ℓQ ℓQ'
    rT = renamingTerm Q

  Ne[_] : ∀ A → Presheafᴰ (nerve Q ⟅ A ⟆) (Unitᴰ (REN Q)) ℓ
  Ne[ A ] .F-ob (Γ , _ , t) =
    (Σ[ n ∈ Ne Q Γ A ] (⌈_⌉ₑ Q n ≡ t))
    , isSetΣ isSetNe (λ _ → isProp→isSet (isSetExpr _ _))
  Ne[ A ] .F-hom (ρ , _ , e) (n , p) =
    renNe Q ρ n
    , renNe-natural Q ρ n ∙ cong (rT ρ ⋆ₑ_) p ∙ e
  Ne[ A ] .F-id = funExt λ (n , p) →
    ΣPathPProp (λ _ → isSetExpr _ _) (renNe-id Q n)
  Ne[ A ] .F-seq f g = funExt λ (n , p) →
    ΣPathPProp (λ _ → isSetExpr _ _)
      (sym (renNe-seq Q (g .fst) (f .fst) n))

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  private
    module Q = ×⇒Quiver Q
    ℓ = ℓ-max ℓQ ℓQ'
    rT = renamingTerm Q
    module Motive = CartesianClosedCategoryᴰ (NbEMotive Q)

  open NfPresheaf Q
  open NePresheaf Q

  genNe : ∀ e → Motive.Cᴰ.Hom[ ↑ₑ e ][ Nf[ Q.dom e ] , Ne[ Q.cod e ] ]
  genNe e = mkPsh ℓ
    ( (λ Γ z → (z .fst ⋆ₑ (↑ₑ e) , gen e (z .snd .fst)
        , cong (_⋆ₑ (↑ₑ e)) (z .snd .snd)) , refl)
    , λ ρ → funExt λ z → ΣPathP (⋆ₑAssoc _ _ _
        , ΣPathPProp (λ _ → isSetExpr _ _) refl))

  fstNe : ∀ {A B} → Motive.Cᴰ.Hom[ π₁ ][ Ne[ A × B ] , Ne[ A ] ]
  fstNe = mkPsh ℓ
    ( (λ Γ z → (z .fst ⋆ₑ π₁ , fst' (z .snd .fst)
        , cong (_⋆ₑ π₁) (z .snd .snd)) , refl)
    , λ ρ → funExt λ z → ΣPathP (⋆ₑAssoc _ _ _
        , ΣPathPProp (λ _ → isSetExpr _ _) refl))

  sndNe : ∀ {A B} → Motive.Cᴰ.Hom[ π₂ ][ Ne[ A × B ] , Ne[ B ] ]
  sndNe = mkPsh ℓ
    ( (λ Γ z → (z .fst ⋆ₑ π₂ , snd' (z .snd .fst)
        , cong (_⋆ₑ π₂) (z .snd .snd)) , refl)
    , λ ρ → funExt λ z → ΣPathP (⋆ₑAssoc _ _ _
        , ΣPathPProp (λ _ → isSetExpr _ _) refl))

  module _ {A B : Q.obExpr} where
    private
      AppDom = Motive.bpᴰ Ne[ A ⇒ B ] Nf[ A ] .fst
    module _ {Γ} (z : fst (∫ᴾ ℓ AppDom .F-ob Γ)) where
      appFn : Ne Q Γ (A ⇒ B)
      appFn = z .snd .fst .fst .snd .fst .snd .fst
      appArg : Nf Q Γ A
      appArg = z .snd .snd .fst .snd .fst .snd .fst
      appFn≡ : ⌈_⌉ₑ Q appFn ≡ z .fst ⋆ₑ π₁
      appFn≡ = z .snd .fst .fst .snd .fst .snd .snd
        ∙ z .snd .fst .fst .snd .snd
        ∙ cong (_⋆ₑ π₁) (z .snd .fst .snd)
      appArg≡ : ⌈_⌉ Q appArg ≡ z .fst ⋆ₑ π₂
      appArg≡ = z .snd .snd .fst .snd .fst .snd .snd
        ∙ z .snd .snd .fst .snd .snd
        ∙ cong (_⋆ₑ π₂) (z .snd .snd .snd)

    appNe : Motive.Cᴰ.Hom[ eval ][ AppDom , Ne[ B ] ]
    appNe = mkPsh ℓ
      ( (λ Γ z → (z .fst ⋆ₑ eval
          , app (appFn z) (appArg z)
          , cong (_⋆ₑ eval) (cong₂ ⟨_,_⟩ (appFn≡ z) (appArg≡ z) ∙ sym ×η))
          , refl)
      , λ ρ → funExt λ z → ΣPathP (⋆ₑAssoc _ _ _
          , ΣPathPProp (λ _ → isSetExpr _ _) refl))
