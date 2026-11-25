{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianClosedCategory.NormalForms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Base
open import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver

open import Gluing.CartesianClosedCategory.Renamings

private
  variable ℓQ ℓQ' : Level

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  private
    module Q = ×⇒Quiver Q
    ℓ = ℓ-max ℓQ ℓQ'
    rT = renamingTerm Q
    idRen = λ {Γ} → REN Q .Category.id {Γ}
    _⋆Ren_ = λ {Θ Δ Γ} → REN Q .Category._⋆_ {Θ} {Δ} {Γ}

  data Nf (Γ : Ctx Q) : Q.obExpr → Type ℓ
  data Ne (Γ : Ctx Q) : Q.obExpr → Type ℓ

  data Nf Γ where
    ne : ∀ {o} → Ne Γ (↑ o) → Nf Γ (↑ o)
    lam : ∀ {A B} → Nf (Γ × (↑ A)) B → Nf Γ (A ⇒ B)
    pair : ∀ {A B} → Nf Γ A → Nf Γ B → Nf Γ (A × B)
    unit : Nf Γ ⊤
    isSetNf : ∀ {A} → isSet (Nf Γ A)

  data Ne Γ where
    var : ∀ {A} → Var Q Γ A → Ne Γ A
    app : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    fst' : ∀ {A B} → Ne Γ (A × B) → Ne Γ A
    snd' : ∀ {A B} → Ne Γ (A × B) → Ne Γ B
    gen : ∀ e → Nf Γ (Q.dom e) → Ne Γ (Q.cod e)
    isSetNe : ∀ {A} → isSet (Ne Γ A)

  ⌈_⌉ : ∀ {Γ A} → Nf Γ A → Term Q Γ A
  ⌈_⌉ₑ : ∀ {Γ A} → Ne Γ A → Term Q Γ A
  ⌈ ne n ⌉ = ⌈ n ⌉ₑ
  ⌈ lam t ⌉ = λ- ⌈ t ⌉
  ⌈ pair t u ⌉ = ⟨ ⌈ t ⌉ , ⌈ u ⌉ ⟩
  ⌈ unit ⌉ = !ₑ
  ⌈ isSetNf t u p q i j ⌉ =
    isSetExpr ⌈ t ⌉ ⌈ u ⌉ (cong ⌈_⌉ p) (cong ⌈_⌉ q) i j
  ⌈ var v ⌉ₑ = rT v
  ⌈ app n t ⌉ₑ = ⟨ ⌈ n ⌉ₑ , ⌈ t ⌉ ⟩ ⋆ₑ eval
  ⌈ fst' n ⌉ₑ = ⌈ n ⌉ₑ ⋆ₑ π₁
  ⌈ snd' n ⌉ₑ = ⌈ n ⌉ₑ ⋆ₑ π₂
  ⌈ gen e t ⌉ₑ = ⌈ t ⌉ ⋆ₑ (↑ₑ e)
  ⌈ isSetNe n m p q i j ⌉ₑ =
    isSetExpr ⌈ n ⌉ₑ ⌈ m ⌉ₑ (cong ⌈_⌉ₑ p) (cong ⌈_⌉ₑ q) i j

  renNf : ∀ {Δ Γ A} → Ren Q Δ Γ → Nf Γ A → Nf Δ A
  renNe : ∀ {Δ Γ A} → Ren Q Δ Γ → Ne Γ A → Ne Δ A
  renNf ρ (ne n) = ne (renNe ρ n)
  renNf ρ (lam {A = A} t) = lam (renNf (extendRenaming Q A ρ) t)
  renNf ρ (pair t u) = pair (renNf ρ t) (renNf ρ u)
  renNf ρ unit = unit
  renNf ρ (isSetNf t u p q i j) =
    isSetNf (renNf ρ t) (renNf ρ u) (cong (renNf ρ) p) (cong (renNf ρ) q) i j
  renNe ρ (var v) = var (ren Q ρ v)
  renNe ρ (app n t) = app (renNe ρ n) (renNf ρ t)
  renNe ρ (fst' n) = fst' (renNe ρ n)
  renNe ρ (snd' n) = snd' (renNe ρ n)
  renNe ρ (gen e t) = gen e (renNf ρ t)
  renNe ρ (isSetNe n m p q i j) =
    isSetNe (renNe ρ n) (renNe ρ m) (cong (renNe ρ) p) (cong (renNe ρ) q) i j

  pairing-natural : ∀ {Δ Γ A B} (f : Expr Q Δ Γ) (a : Expr Q Γ A)
    (b : Expr Q Γ B) → f ⋆ₑ ⟨ a , b ⟩ ≡ ⟨ f ⋆ₑ a , f ⋆ₑ b ⟩
  pairing-natural f a b =
    ×η
    ∙ cong₂ ⟨_,_⟩ (⋆ₑAssoc _ _ _ ∙ cong (f ⋆ₑ_) ×β₁)
        (⋆ₑAssoc _ _ _ ∙ cong (f ⋆ₑ_) ×β₂)

  lam-natural : ∀ {Δ Γ A B} (f : Expr Q Δ Γ) (b : Expr Q (Γ × A) B)
    → f ⋆ₑ (λ- b) ≡ λ- (⟨ π₁ ⋆ₑ f , π₂ ⟩ ⋆ₑ b)
  lam-natural {A = A} f b =
    λη (f ⋆ₑ (λ- b))
    ∙ cong λ-_
        ( cong (_⋆ₑ eval)
            ( cong₂ ⟨_,_⟩ (sym (⋆ₑAssoc π₁ f (λ- b))) refl
            ∙ cong₂ ⟨_,_⟩
                (cong (_⋆ₑ (λ- b)) (sym ×β₁) ∙ ⋆ₑAssoc lifted π₁ (λ- b))
                (sym ×β₂)
            ∙ sym (pairing-natural lifted (π₁ ⋆ₑ (λ- b)) π₂))
        ∙ ⋆ₑAssoc lifted _ eval
        ∙ cong (lifted ⋆ₑ_) (λβ b))
    where
    lifted : Expr Q (_ × A) (_ × A)
    lifted = ⟨ π₁ ⋆ₑ f , π₂ ⟩

  renNf-natural : ∀ {Δ Γ A} (ρ : Ren Q Δ Γ) (t : Nf Γ A)
    → ⌈ renNf ρ t ⌉ ≡ rT ρ ⋆ₑ ⌈ t ⌉
  renNe-natural : ∀ {Δ Γ A} (ρ : Ren Q Δ Γ) (n : Ne Γ A)
    → ⌈ renNe ρ n ⌉ₑ ≡ rT ρ ⋆ₑ ⌈ n ⌉ₑ
  renNf-natural ρ (ne n) = renNe-natural ρ n
  renNf-natural ρ (lam {A = A} t) =
    cong λ-_ (renNf-natural (extendRenaming Q A ρ) t)
    ∙ sym (lam-natural _ ⌈ t ⌉)
  renNf-natural ρ (pair t u) =
    cong₂ ⟨_,_⟩ (renNf-natural ρ t) (renNf-natural ρ u)
    ∙ sym (pairing-natural _ _ _)
  renNf-natural ρ unit = sym (⊤η _)
  renNf-natural ρ (isSetNf t u p q i j) =
    isSet→SquareP
      (λ i j → isOfHLevelPath 2 isSetExpr
        ⌈ renNf ρ (isSetNf t u p q i j) ⌉
        (rT ρ ⋆ₑ ⌈ isSetNf t u p q i j ⌉))
      (λ j → renNf-natural ρ (p j)) (λ j → renNf-natural ρ (q j))
      (λ i → renNf-natural ρ t) (λ i → renNf-natural ρ u) i j
  renNe-natural ρ (var v) = cong rT (ren≡ Q ρ v)
  renNe-natural ρ (app n t) =
    cong (_⋆ₑ eval) (cong₂ ⟨_,_⟩ (renNe-natural ρ n) (renNf-natural ρ t)
      ∙ sym (pairing-natural _ _ _))
    ∙ ⋆ₑAssoc _ _ _
  renNe-natural ρ (fst' n) = cong (_⋆ₑ π₁) (renNe-natural ρ n) ∙ ⋆ₑAssoc _ _ _
  renNe-natural ρ (snd' n) = cong (_⋆ₑ π₂) (renNe-natural ρ n) ∙ ⋆ₑAssoc _ _ _
  renNe-natural ρ (gen e t) =
    cong (_⋆ₑ (↑ₑ e)) (renNf-natural ρ t) ∙ ⋆ₑAssoc _ _ _
  renNe-natural ρ (isSetNe n m p q i j) =
    isSet→SquareP
      (λ i j → isOfHLevelPath 2 isSetExpr
        ⌈ renNe ρ (isSetNe n m p q i j) ⌉ₑ
        (rT ρ ⋆ₑ ⌈ isSetNe n m p q i j ⌉ₑ))
      (λ j → renNe-natural ρ (p j)) (λ j → renNe-natural ρ (q j))
      (λ i → renNe-natural ρ n) (λ i → renNe-natural ρ m) i j

  renNf-id : ∀ {Γ A} (t : Nf Γ A) → renNf idRen t ≡ t
  renNe-id : ∀ {Γ A} (n : Ne Γ A) → renNe idRen n ≡ n
  renNf-id (ne n) = cong ne (renNe-id n)
  renNf-id (lam {A = A} t) =
    cong lam (cong (λ ρ → renNf ρ t) (extend-id Q A) ∙ renNf-id t)
  renNf-id (pair t u) = cong₂ pair (renNf-id t) (renNf-id u)
  renNf-id unit = refl
  renNf-id (isSetNf t u p q i j) =
    isSet→SquareP (λ i j → isOfHLevelPath 2 isSetNf
        (renNf idRen (isSetNf t u p q i j)) (isSetNf t u p q i j))
      (λ j → renNf-id (p j)) (λ j → renNf-id (q j))
      (λ i → renNf-id t) (λ i → renNf-id u) i j
  renNe-id (var v) = cong var (renId Q v)
  renNe-id (app n t) = cong₂ app (renNe-id n) (renNf-id t)
  renNe-id (fst' n) = cong fst' (renNe-id n)
  renNe-id (snd' n) = cong snd' (renNe-id n)
  renNe-id (gen g t) = cong (gen g) (renNf-id t)
  renNe-id (isSetNe n m p q i j) =
    isSet→SquareP (λ i j → isOfHLevelPath 2 isSetNe
        (renNe idRen (isSetNe n m p q i j)) (isSetNe n m p q i j))
      (λ j → renNe-id (p j)) (λ j → renNe-id (q j))
      (λ i → renNe-id n) (λ i → renNe-id m) i j

  renNf-seq : ∀ {Θ Δ Γ A} (σ : Ren Q Θ Δ) (ρ : Ren Q Δ Γ) (t : Nf Γ A)
    → renNf σ (renNf ρ t) ≡ renNf (σ ⋆Ren ρ) t
  renNe-seq : ∀ {Θ Δ Γ A} (σ : Ren Q Θ Δ) (ρ : Ren Q Δ Γ) (n : Ne Γ A)
    → renNe σ (renNe ρ n) ≡ renNe (σ ⋆Ren ρ) n
  renNf-seq σ ρ (ne n) = cong ne (renNe-seq σ ρ n)
  renNf-seq σ ρ (lam {A = A} t) =
    cong lam (renNf-seq (extendRenaming Q A σ) (extendRenaming Q A ρ) t
      ∙ cong (λ τ → renNf τ t) (extend-seq Q A σ ρ))
  renNf-seq σ ρ (pair t u) = cong₂ pair (renNf-seq σ ρ t) (renNf-seq σ ρ u)
  renNf-seq σ ρ unit = refl
  renNf-seq σ ρ (isSetNf t u p q i j) =
    isSet→SquareP (λ i j → isOfHLevelPath 2 isSetNf
        (renNf σ (renNf ρ (isSetNf t u p q i j)))
        (renNf (σ ⋆Ren ρ) (isSetNf t u p q i j)))
      (λ j → renNf-seq σ ρ (p j)) (λ j → renNf-seq σ ρ (q j))
      (λ i → renNf-seq σ ρ t) (λ i → renNf-seq σ ρ u) i j
  renNe-seq σ ρ (var v) = cong var (ren⋆ Q σ ρ v)
  renNe-seq σ ρ (app n t) = cong₂ app (renNe-seq σ ρ n) (renNf-seq σ ρ t)
  renNe-seq σ ρ (fst' n) = cong fst' (renNe-seq σ ρ n)
  renNe-seq σ ρ (snd' n) = cong snd' (renNe-seq σ ρ n)
  renNe-seq σ ρ (gen g t) = cong (gen g) (renNf-seq σ ρ t)
  renNe-seq σ ρ (isSetNe n m p q i j) =
    isSet→SquareP (λ i j → isOfHLevelPath 2 isSetNe
        (renNe σ (renNe ρ (isSetNe n m p q i j)))
        (renNe (σ ⋆Ren ρ) (isSetNe n m p q i j)))
      (λ j → renNe-seq σ ρ (p j)) (λ j → renNe-seq σ ρ (q j))
      (λ i → renNe-seq σ ρ n) (λ i → renNe-seq σ ρ m) i j
