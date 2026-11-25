module Cubical.Categories.Instances.Free.CartesianCategory.Variables where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Instances.Free.CartesianCategory.Base
open import Cubical.Categories.Instances.Free.CartesianCategory.UncurriedElim

private
  variable ℓ : Level

Type→×Quiver : Type ℓ → ×Quiver ℓ ℓ-zero
Type→×Quiver X .×Quiver.ob = X
Type→×Quiver X .×Quiver.Q .QuiverOver.mor = ⊥*
Type→×Quiver X .×Quiver.Q .QuiverOver.dom ()
Type→×Quiver X .×Quiver.Q .QuiverOver.cod ()

module _ (X : Type ℓ) where
  private
    Q = Type→×Quiver X
    Ctx = ×Quiver.Expr Q
    Ren = Exp Q

  Var : Ctx → X → Type ℓ
  Var Γ A = Ren Γ (↑ A)

  private
    pairing-natural : ∀ {Θ Δ Γ Γ'} (f : Ren Θ Δ) (a : Ren Δ Γ) (b : Ren Δ Γ')
      → f ⋆ₑ ⟨ a , b ⟩ ≡ ⟨ f ⋆ₑ a , f ⋆ₑ b ⟩
    pairing-natural f a b =
      ×η
      ∙ cong₂ ⟨_,_⟩ (⋆ₑAssoc _ _ _ ∙ cong (f ⋆ₑ_) ×β₁)
          (⋆ₑAssoc _ _ _ ∙ cong (f ⋆ₑ_) ×β₂)

  module _ (Γ : Ctx) where
    Env : Functor (|FreeCartesianCategory| Q) (SET ℓ)
    Env = rec Q SETCC (mkInterpᴰ (λ A → Var Γ A , isSetExp) λ ())

    embed : ∀ Θ → fst (Env ⟅ Θ ⟆) → Ren Γ Θ
    embed (↑ A) v = v
    embed (Θ × Θ') (e , e') = ⟨ embed Θ e , embed Θ' e' ⟩
    embed ⊤ _ = !ₑ

    EmbedNatural : ∀ {Θ Θ'} → Ren Θ Θ' → Type ℓ
    EmbedNatural {Θ} {Θ'} u =
      ∀ e → embed Θ' ((Env ⟪ u ⟫) e) ≡ embed Θ e ⋆ₑ u

    private
      seqCase : ∀ {Θ Θ' Θ''} (u : Ren Θ Θ') (u' : Ren Θ' Θ'')
        → EmbedNatural u → EmbedNatural u' → EmbedNatural (u ⋆ₑ u')
      seqCase u u' ih ih' e = ih' ((Env ⟪ u ⟫) e)
        ∙ cong (_⋆ₑ u') (ih e) ∙ ⋆ₑAssoc _ u u'

      idCase : ∀ {Θ} → EmbedNatural {Θ} idₑ
      idCase e = sym (⋆ₑIdR _)

      π₁Case : ∀ {Θ Θ'} → EmbedNatural {Θ × Θ'} π₁
      π₁Case e = sym ×β₁

      π₂Case : ∀ {Θ Θ'} → EmbedNatural {Θ × Θ'} π₂
      π₂Case e = sym ×β₂

      pairCase : ∀ {Θ Θ' Θ''} (u : Ren Θ Θ') (u' : Ren Θ Θ'')
        → EmbedNatural u → EmbedNatural u' → EmbedNatural ⟨ u , u' ⟩
      pairCase u u' ih ih' e = cong₂ ⟨_,_⟩ (ih e) (ih' e)
        ∙ sym (pairing-natural _ u u')

      pathCase : ∀ {Θ Θ'} {u u' : Ren Θ Θ'} (p : u ≡ u')
        (a : EmbedNatural u) (b : EmbedNatural u') e
        → PathP (λ i → embed Θ' ((Env ⟪ p i ⟫) e) ≡ embed Θ e ⋆ₑ p i)
            (a e) (b e)
      pathCase {Θ} {Θ'} p a b e = isProp→PathP
        (λ i → isSetExp (embed Θ' ((Env ⟪ p i ⟫) e)) (embed Θ e ⋆ₑ p i))
        (a e) (b e)

    embed-natural : ∀ {Θ Θ'} (u : Ren Θ Θ') → EmbedNatural u
    embed-natural (↑ₑ ())
    embed-natural idₑ = idCase
    embed-natural (u ⋆ₑ u') =
      seqCase u u' (embed-natural u) (embed-natural u')
    embed-natural (⋆ₑIdL u i) e = pathCase (⋆ₑIdL u)
      (seqCase idₑ u idCase (embed-natural u)) (embed-natural u) e i
    embed-natural (⋆ₑIdR u i) e = pathCase (⋆ₑIdR u)
      (seqCase u idₑ (embed-natural u) idCase) (embed-natural u) e i
    embed-natural (⋆ₑAssoc u u' u'' i) e = pathCase (⋆ₑAssoc u u' u'')
      (seqCase (u ⋆ₑ u') u'' (seqCase u u' ih ih') ih'')
      (seqCase u (u' ⋆ₑ u'') ih (seqCase u' u'' ih' ih'')) e i
      where
      ih = embed-natural u
      ih' = embed-natural u'
      ih'' = embed-natural u''
    embed-natural {Θ} {Θ'} (isSetExp u u' p q i j) e =
      isSet→SquareP (λ i j → isProp→isSet (isSetExp
          (embed Θ' ((Env ⟪ isSetExp u u' p q i j ⟫) e))
          (embed Θ e ⋆ₑ isSetExp u u' p q i j)))
        (λ j → embed-natural (p j) e) (λ j → embed-natural (q j) e)
        (λ i → embed-natural u e) (λ i → embed-natural u' e) i j
    embed-natural !ₑ e = sym (⊤η _)
    embed-natural (⊤η u i) e =
      pathCase (⊤η u) (embed-natural u) (λ e → sym (⊤η _)) e i
    embed-natural π₁ = π₁Case
    embed-natural π₂ = π₂Case
    embed-natural ⟨ u , u' ⟩ =
      pairCase u u' (embed-natural u) (embed-natural u')
    embed-natural (×β₁ {t = u} {t' = u'} i) e = pathCase ×β₁
      (seqCase ⟨ u , u' ⟩ π₁
        (pairCase u u' (embed-natural u) (embed-natural u')) π₁Case)
      (embed-natural u) e i
    embed-natural (×β₂ {t = u} {t' = u'} i) e = pathCase ×β₂
      (seqCase ⟨ u , u' ⟩ π₂
        (pairCase u u' (embed-natural u) (embed-natural u')) π₂Case)
      (embed-natural u') e i
    embed-natural (×η {t = u} i) e = pathCase ×η (embed-natural u)
      (pairCase (u ⋆ₑ π₁) (u ⋆ₑ π₂) (seqCase u π₁ (embed-natural u) π₁Case)
        (seqCase u π₂ (embed-natural u) π₂Case)) e i

    idEnv : ∀ Θ → (∀ {Θ'} → Ren Θ Θ' → Ren Γ Θ') → fst (Env ⟅ Θ ⟆)
    idEnv (↑ A) k = k idₑ
    idEnv (Θ × (↑ A)) k = idEnv Θ (λ u → k (π₁ ⋆ₑ u)) , k π₂
    idEnv (Θ × Θ'@(_ × _)) k =
      idEnv Θ (λ u → k (π₁ ⋆ₑ u)) , idEnv Θ' (λ u → k (π₂ ⋆ₑ u))
    idEnv (Θ × ⊤) k = idEnv Θ (λ u → k (π₁ ⋆ₑ u)) , tt*
    idEnv ⊤ k = tt*

    private
      projCase : ∀ {Θ Θ'} (k : ∀ {Θ''} → Ren Θ Θ'' → Ren Γ Θ'')
        (nat : ∀ {Θ'' Θ'''} (u : Ren Θ Θ'') (u' : Ren Θ'' Θ''')
          → k (u ⋆ₑ u') ≡ k u ⋆ₑ u')
        (π : Ren Θ Θ')
        → ∀ {Θ'' Θ'''} (u : Ren Θ' Θ'') (u' : Ren Θ'' Θ''')
          → k (π ⋆ₑ (u ⋆ₑ u')) ≡ k (π ⋆ₑ u) ⋆ₑ u'
      projCase k nat π u u' = cong k (sym (⋆ₑAssoc π u u')) ∙ nat (π ⋆ₑ u) u'

      projId : ∀ {Θ Θ'} (k : ∀ {Θ''} → Ren Θ Θ'' → Ren Γ Θ'')
        (nat : ∀ {Θ'' Θ'''} (u : Ren Θ Θ'') (u' : Ren Θ'' Θ''')
          → k (u ⋆ₑ u') ≡ k u ⋆ₑ u')
        (π : Ren Θ Θ') → k (π ⋆ₑ idₑ) ≡ k idₑ ⋆ₑ π
      projId k nat π = cong k (⋆ₑIdR π ∙ sym (⋆ₑIdL π)) ∙ nat idₑ π

    embed-idEnv : ∀ Θ (k : ∀ {Θ'} → Ren Θ Θ' → Ren Γ Θ')
      → (∀ {Θ' Θ''} (u : Ren Θ Θ') (u' : Ren Θ' Θ'')
        → k (u ⋆ₑ u') ≡ k u ⋆ₑ u')
      → embed Θ (idEnv Θ k) ≡ k idₑ
    embed-idEnv (↑ A) k nat = refl
    embed-idEnv (Θ × (↑ A)) k nat =
      cong₂ ⟨_,_⟩
        (embed-idEnv Θ _ (projCase k nat π₁) ∙ projId k nat π₁)
        (cong k (sym (⋆ₑIdL π₂)) ∙ nat idₑ π₂)
      ∙ sym ×η
    embed-idEnv (Θ × Θ'@(_ × _)) k nat =
      cong₂ ⟨_,_⟩
        (embed-idEnv Θ _ (projCase k nat π₁) ∙ projId k nat π₁)
        (embed-idEnv Θ' _ (projCase k nat π₂) ∙ projId k nat π₂)
      ∙ sym ×η
    embed-idEnv (Θ × ⊤) k nat =
      cong₂ ⟨_,_⟩
        (embed-idEnv Θ _ (projCase k nat π₁) ∙ projId k nat π₁)
        (embed-idEnv ⊤ _ (projCase k nat π₂) ∙ projId k nat π₂)
      ∙ sym ×η
    embed-idEnv ⊤ k nat = sym (⊤η _)

    normVar : ∀ {A} → Var Γ A → Var Γ A
    normVar v = (Env ⟪ v ⟫) (idEnv Γ (λ u → u))

    normVar≡ : ∀ {A} (v : Var Γ A) → normVar v ≡ v
    normVar≡ v = embed-natural v (idEnv Γ (λ u → u))
      ∙ cong (_⋆ₑ v) (embed-idEnv Γ (λ u → u) (λ _ _ → refl)) ∙ ⋆ₑIdL v
