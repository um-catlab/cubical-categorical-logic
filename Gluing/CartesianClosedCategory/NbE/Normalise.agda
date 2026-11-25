{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianClosedCategory.NbE.Normalise where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation.Base hiding (_⇒_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Instances.Reindex.ChosenReind
open import Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Base
open import
  Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Quantifier
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Base
open import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
  using (_×_; ↑_; ⊤)
open import Cubical.Categories.Instances.Free.CartesianCategory.Base
  using (FreeCartesianCategory)
open import Cubical.Categories.Instances.Free.CartesianCategory.Variables
  using (normVar; normVar≡)
open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.UncurriedElim

open import Gluing.CartesianClosedCategory.Renamings
open import Gluing.CartesianClosedCategory.NormalForms
open import Gluing.CartesianClosedCategory.NbE.Base
open import Gluing.CartesianClosedCategory.NbE.Neutral
open import Gluing.CartesianClosedCategory.NbE.Reify

private
  variable ℓQ ℓQ' : Level

open Functor
open NatTrans
open Section

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  open NfPresheaf Q
  open NePresheaf Q

  private
    module Q = ×⇒Quiver Q
    ℓ = ℓ-max ℓQ ℓQ'
    N = nerve Q
    rT = renamingTerm Q
    module RENCC = CartesianCategory (FreeCartesianCategory (RenQuiver Q))
    ctx = contextType Q
    Motive = NbEMotive Q
    module GL = ChosenReindNotation (CartesianClosedCategoryᴰ.Cᴰ Motive)
      ⦃ reindexReind (PSHCod ℓ) N ⦄

  ı-hom : ∀ e → GL.Hom[ ↑ₑ e ][ Gl Q (Q.dom e)
    , Gl Q (Q.cod e) ]
  ı-hom e = GL.reind⟨ ⋆ₑIdR _ ∙ ⋆ₑIdL _ ⟩
    ((reify Q (Q.dom e) GL.⋆ᴰ genNe Q e)
      GL.⋆ᴰ reflect Q (Q.cod e))

  ı : Interpᴰ Q Motive
  ı = interpᴰ (λ o → Nf[ ↑ o ]) ı-hom

  NbESection : Section N (PSHCod ℓ)
  NbESection = elimLocal Q (nerve Q , nerve-pres-bp Q)
    (PSHCodCCCⱽ ℓQ') ı

  env : ∀ {Δ} Γ (ρ : Ren Q Δ Γ)
    → Σ[ x ∈ fst (∫ᴾ ℓ (Gl Q (ctx Γ)) .F-ob Δ) ] x .fst ≡ rT ρ
  env (↑ A) ρ = reflect Q A .fst .N-ob _ x
    , tri≡ Q {f = idₑ} {P = Ne[ A ]} {P' = Gl Q A} (reflect Q A) x
      ∙ ⋆ₑIdR _
    where
    x : fst (∫ᴾ ℓ Ne[ A ] .F-ob _)
    x = rT ρ , var (normVar Q.obExpr _ ρ)
      , cong rT (normVar≡ Q.obExpr _ ρ)
  env (Γ × Γ') ρ = (rT ρ
    , ((rT ρ , env Γ (ρ RENCC.⋆ RENCC.π₁)) , refl)
    , ((rT ρ , env Γ' (ρ RENCC.⋆ RENCC.π₂)) , refl)) , refl
  env ⊤ ρ = (rT ρ , tt*) , refl

  module _ {Γ A} (t : Term Q Γ A) where
    private
      envElt : fst (∫ᴾ ℓ (Gl Q (ctx Γ)) .F-ob Γ)
      envElt = env Γ RENCC.id .fst

      value : fst (∫ᴾ ℓ (Gl Q A) .F-ob Γ)
      value = NbESection .F-homᴰ t .fst .N-ob Γ envElt

    normalise : Nf Q Γ A
    normalise = nfOf Q {A} {Gl Q A} (reify Q A) value

    soundness : ⌈_⌉ Q normalise ≡ t
    soundness = nfOf≡ Q {A} {Gl Q A} (reify Q A) value
      ∙ tri≡ Q {f = t} {P = Gl Q (ctx Γ)} {P' = Gl Q A}
          (NbESection .F-homᴰ t) envElt
      ∙ cong (_⋆ₑ t) (env Γ RENCC.id .snd) ∙ ⋆ₑIdL t

private
  module Examples where
    a : Unit
    a = tt

    Q : ×⇒Quiver ℓ-zero ℓ-zero
    Q .×⇒Quiver.ob = Unit
    Q .×⇒Quiver.Q .QuiverOver.mor = ⊥
    Q .×⇒Quiver.Q .QuiverOver.dom ()
    Q .×⇒Quiver.Q .QuiverOver.cod ()

    Tm = Expr Q

    app' : ∀ {Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    app' t u = ⟨ t , u ⟩ ⋆ₑ eval

    v₀ : ∀ {Γ A} → Tm (Γ × A) A
    v₀ = π₂

    v₁ : ∀ {Γ A B} → Tm ((Γ × A) × B) A
    v₁ = π₁ ⋆ₑ π₂

    v₂ : ∀ {Γ A B C} → Tm (((Γ × A) × B) × C) A
    v₂ = π₁ ⋆ₑ (π₁ ⋆ₑ π₂)

    nf : ∀ Γ {A} → Tm (contextType Q Γ) A → Nf Q Γ A
    nf Γ = normalise Q

    z₁ : ∀ {Γ A B} → Var Q ((Γ × (↑ A)) × (↑ B)) A
    z₁ = vs Q (vz Q)

    x₀ : ∀ {Γ} → Nf Q (Γ × (↑ (↑ a))) (↑ a)
    x₀ = ne (var (vz Q))

    K : ∀ {Γ} A B → Tm Γ (A ⇒ (B ⇒ A))
    K A B = λ- (λ- v₁)

    S : ∀ {Γ} A B C → Tm Γ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
    S A B C = λ- (λ- (λ- (app' (app' v₂ v₀) (app' v₁ v₀))))

    _ : nf ⊤ (app' (app' (S (↑ a) ((↑ a) ⇒ (↑ a)) (↑ a))
          (K (↑ a) ((↑ a) ⇒ (↑ a)))) (K (↑ a) (↑ a)))
      ≡ lam x₀
    _ = refl

    _ : nf ⊤ {((↑ a) ⇒ (↑ a)) ⇒ ((↑ a) ⇒ (↑ a))}
          (λ- (λ- (app' v₁ (app' v₁ v₀))))
      ≡ lam (lam (ne (app (var z₁) (ne (app (var z₁) x₀)))))
    _ = refl

    _ : nf (⊤ × (↑ ((↑ a) ⇒ (↑ a)))) v₀ ≡ lam (ne (app (var z₁) x₀))
    _ = refl
