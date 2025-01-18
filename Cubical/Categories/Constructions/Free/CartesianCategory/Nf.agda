module Cubical.Categories.Constructions.Free.CartesianCategory.Nf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver

open import Cubical.HITs.SetTruncation

private
  variable
    ℓq ℓq' : Level

module _ (Q : ×Quiver ℓq ℓq')
  where
  open Category
  private
    module Q = ×QuiverNotation Q

  data NormalForm : (Γ τ : Q.Ob) → Type (ℓ-max ℓq ℓq')
  data NeutralTerm : (Γ τ : Q.Ob) → Type (ℓ-max ℓq ℓq')

  data NeutralTerm where
    var : ∀{τ} → NeutralTerm τ τ
    proj₁ : ∀{Γ τ₁ τ₂} → NeutralTerm Γ (τ₁ × τ₂) → NeutralTerm Γ τ₁
    proj₂ : ∀{Γ τ₁ τ₂} → NeutralTerm Γ (τ₁ × τ₂) → NeutralTerm Γ τ₂
    symb : ∀{Γ} (f : Q.mor) → NormalForm Γ (Q.dom f) → NeutralTerm Γ (↑ (Q.cod f))

  data NormalForm where
    -- shift only at ground types to enforce η-long normal forms
    shift : ∀{Γ τ} → NeutralTerm Γ (↑ τ) → NormalForm Γ (↑ τ)
    pair : ∀{Γ τ₁ τ₂} → NormalForm Γ τ₁ → NormalForm Γ τ₂ → NormalForm Γ (τ₁ × τ₂)
    uniq : ∀{Γ} → NormalForm Γ ⊤

  -- this is the "type directed" shift
  SHIFT : ∀{Γ τ} → NeutralTerm Γ τ → NormalForm Γ τ
  SHIFT {τ = ↑ _} ne = shift ne
  SHIFT {τ = τ₁ × τ₂} ne = pair (SHIFT $ proj₁ ne) (SHIFT $ proj₂ ne)
  SHIFT {τ = ⊤} _ = uniq
  -- there's also a constructor-directed (syntax directed?) shift, but it doesn't obviously have any nice properties?

  ID : ∀{τ} → NormalForm τ τ
  ID = SHIFT var

  PROJ₁ : ∀{Γ τ₁ τ₂} → NormalForm Γ (τ₁ × τ₂) → NormalForm Γ τ₁
  PROJ₁ (pair n₁ _) = n₁

  PROJ₂ : ∀{Γ τ₁ τ₂} → NormalForm Γ (τ₁ × τ₂) → NormalForm Γ τ₂
  PROJ₂ (pair _ n₂) = n₂

  -- substitution, in composition order (*not* "diagramatic" order)
  Nf/Nf : ∀{Γ Δ τ} → NormalForm Δ τ → NormalForm Γ Δ → NormalForm Γ τ
  Ne/Nf : ∀{Γ Δ τ} → NeutralTerm Δ τ → NormalForm Γ Δ → NormalForm Γ τ
  Nf/Ne : ∀{Γ Δ τ} → NormalForm Δ τ → NeutralTerm Γ Δ → NormalForm Γ τ
  Ne/Ne : ∀{Γ Δ τ} → NeutralTerm Δ τ → NeutralTerm Γ Δ → NeutralTerm Γ τ

  Nf/Nf (shift ne) nf = Ne/Nf ne nf
  Nf/Nf (pair nf₁ nf₂) nf₃ = pair (Nf/Nf nf₁ nf₃) (Nf/Nf nf₂ nf₃)
  Nf/Nf uniq nf₂ = uniq

  Ne/Nf var = idfun _
  Ne/Nf (proj₁ ne) nf = PROJ₁ $ Ne/Nf ne nf
  Ne/Nf (proj₂ ne) nf = PROJ₂ $ Ne/Nf ne nf
  Ne/Nf (symb f nf₁) nf₂ = shift $ symb f $ Nf/Nf nf₁ nf₂

  Nf/Ne (shift ne₁) ne₂ = shift $ Ne/Ne ne₁ ne₂
  Nf/Ne (pair nf₁ nf₂) ne = pair (Nf/Ne nf₁ ne) (Nf/Ne nf₂ ne)
  Nf/Ne uniq _ = uniq

  Ne/Ne var = idfun _
  Ne/Ne (proj₁ ne₁) ne₂ = proj₁ $ Ne/Ne ne₁ ne₂
  Ne/Ne (proj₂ ne₁) ne₂ = proj₂ $ Ne/Ne ne₁ ne₂
  Ne/Ne (symb f nf) ne = symb f $ Nf/Ne nf ne
  IDL : ∀{Γ τ} (n : NormalForm Γ τ) → Nf/Nf n ID ≡ n
  IDL-Ne : ∀{Γ τ} (n : NeutralTerm Γ τ) → Ne/Nf n ID ≡ SHIFT n

  IDL (shift ne) = IDL-Ne ne
  IDL (pair nf₁ nf₂) = cong₂ pair (IDL nf₁) (IDL nf₂)
  IDL uniq = refl

  IDL-Ne var = refl
  IDL-Ne (proj₁ ne) = congS PROJ₁ $ IDL-Ne ne
  IDL-Ne (proj₂ ne) = congS PROJ₂ $ IDL-Ne ne
  IDL-Ne (symb f nf) = congS (shift ∘S symb f) $ IDL nf

  _∘proj₁ : ∀{Γ Δ τ} → NeutralTerm Γ τ → NeutralTerm (Γ × Δ) τ
  _∘PROJ₁ : ∀{Γ Δ τ} → NormalForm Γ τ → NormalForm (Γ × Δ) τ

  var ∘proj₁ = proj₁ var
  (proj₁ ne) ∘proj₁ = proj₁ $ ne ∘proj₁
  (proj₂ ne) ∘proj₁ = proj₂ $ ne ∘proj₁
  (symb f nf) ∘proj₁ = symb f $ nf ∘PROJ₁

  (shift ne) ∘PROJ₁ = shift $ ne ∘proj₁
  (pair nf₁ nf₂) ∘PROJ₁ = pair (nf₁ ∘PROJ₁) (nf₂ ∘PROJ₁)
  uniq ∘PROJ₁ = uniq

  _∘proj₂ : ∀{Γ Δ τ} → NeutralTerm Δ τ → NeutralTerm (Γ × Δ) τ
  _∘PROJ₂ : ∀{Γ Δ τ} → NormalForm Δ τ → NormalForm (Γ × Δ) τ

  var ∘proj₂ = proj₂ var
  (proj₁ ne) ∘proj₂ = proj₁ $ ne ∘proj₂
  (proj₂ ne) ∘proj₂ = proj₂ $ ne ∘proj₂
  (symb f nf) ∘proj₂ = symb f $ nf ∘PROJ₂

  (shift ne) ∘PROJ₂ = shift $ ne ∘proj₂
  (pair nf₁ nf₂) ∘PROJ₂ = pair (nf₁ ∘PROJ₂) (nf₂ ∘PROJ₂)
  uniq ∘PROJ₂ = uniq

  -- these types of proofs should somehow be automatic...
  SHIFT-∘proj₁ : ∀{Γ Δ τ} {ne : NeutralTerm Γ τ} → SHIFT {Γ = Γ × Δ} (ne ∘proj₁) ≡ (SHIFT ne) ∘PROJ₁
  SHIFT-∘proj₁ {τ = ↑ _} = refl
  SHIFT-∘proj₁ {τ = τ₁ × τ₂} = cong₂ pair SHIFT-∘proj₁ SHIFT-∘proj₁
  SHIFT-∘proj₁ {τ = ⊤} = refl

  SHIFT-∘proj₂ : ∀{Γ Δ τ} {ne : NeutralTerm Δ τ} → SHIFT {Γ = Γ × Δ} (ne ∘proj₂) ≡ (SHIFT ne) ∘PROJ₂
  SHIFT-∘proj₂ {τ = ↑ _} = refl
  SHIFT-∘proj₂ {τ = τ₁ × τ₂} = cong₂ pair SHIFT-∘proj₂ SHIFT-∘proj₂
  SHIFT-∘proj₂ {τ = ⊤} = refl

  -- ast of pairs with "pointed" NormalForm
  data Embedded Γ τ (n : NormalForm Γ τ) : Q.Ob → Type (ℓ-max ℓq ℓq') where
    root : Embedded Γ τ n τ
    left : ∀{τ' τ''} → Embedded Γ τ n τ' → NormalForm Γ τ'' → Embedded Γ τ n (τ' × τ'')
    right : ∀{τ' τ''} → NormalForm Γ τ' → Embedded Γ τ n τ'' → Embedded Γ τ n (τ' × τ'')

  -- "project" the point
  ⟨_⟩ : ∀{Γ τ n Δ} →
    Embedded Γ τ n Δ → NeutralTerm Δ τ
  ⟨ root ⟩ = var
  ⟨ left e _ ⟩ = ⟨ e ⟩ ∘proj₁
  ⟨ right _ e ⟩ = ⟨ e ⟩ ∘proj₂

  -- "forget" the point
  ∣_∣ : ∀{Γ τ n Δ} →
    Embedded Γ τ n Δ → NormalForm Γ Δ
  ∣_∣ {n = n} root = n
  ∣_∣ (left e nf) = pair ∣ e ∣ nf
  ∣_∣ (right nf e) = pair nf ∣ e ∣

  β₁-Ne/Nf : ∀{Γ τ₁ τ₂ τ₃} →
    (ne : NeutralTerm τ₁ τ₃) →
    (nf₁ : NormalForm Γ τ₁) →
    (nf₂ : NormalForm Γ τ₂) →
    Ne/Nf (ne ∘proj₁) (pair nf₁ nf₂) ≡ Ne/Nf ne nf₁
  β₁-Nf/Nf : ∀{Γ τ₁ τ₂ τ₃} →
    (nf₃ : NormalForm τ₁ τ₃) →
    (nf₁ : NormalForm Γ τ₁) →
    (nf₂ : NormalForm Γ τ₂) →
    Nf/Nf (nf₃ ∘PROJ₁) (pair nf₁ nf₂) ≡ Nf/Nf nf₃ nf₁

  β₁-Ne/Nf var _ _ = refl
  β₁-Ne/Nf (proj₁ ne) _ _ = congS PROJ₁ $ β₁-Ne/Nf ne _ _
  β₁-Ne/Nf (proj₂ ne) _ _ = congS PROJ₂ $ β₁-Ne/Nf ne _ _
  β₁-Ne/Nf (symb f nf₁) _ _ = congS (shift ∘S symb f) $ β₁-Nf/Nf nf₁ _ _

  β₁-Nf/Nf (shift ne) = β₁-Ne/Nf ne
  β₁-Nf/Nf (pair nf₁ nf₂) _ _ = cong₂ pair (β₁-Nf/Nf nf₁ _ _) (β₁-Nf/Nf nf₂ _ _)
  β₁-Nf/Nf uniq nf₁ nf₂ = refl

  β₂-Ne/Nf : ∀{Γ τ₁ τ₂ τ₃} →
    (ne : NeutralTerm τ₂ τ₃) →
    (nf₁ : NormalForm Γ τ₁) →
    (nf₂ : NormalForm Γ τ₂) →
    Ne/Nf (ne ∘proj₂) (pair nf₁ nf₂) ≡ Ne/Nf ne nf₂
  β₂-Nf/Nf : ∀{Γ τ₁ τ₂ τ₃} →
    (nf₃ : NormalForm τ₂ τ₃) →
    (nf₁ : NormalForm Γ τ₁) →
    (nf₂ : NormalForm Γ τ₂) →
    Nf/Nf (nf₃ ∘PROJ₂) (pair nf₁ nf₂) ≡ Nf/Nf nf₃ nf₂
  β₂-Ne/Nf var _ _ = refl
  β₂-Ne/Nf (proj₁ ne) _ _ = congS PROJ₁ $ β₂-Ne/Nf ne _ _
  β₂-Ne/Nf (proj₂ ne) _ _ = congS PROJ₂ $ β₂-Ne/Nf ne _ _
  β₂-Ne/Nf (symb f nf₁) _ _ = congS (shift ∘S symb f) $ β₂-Nf/Nf nf₁ _ _

  β₂-Nf/Nf (shift ne) = β₂-Ne/Nf ne
  β₂-Nf/Nf (pair nf₁ nf₂) _ _ = cong₂ pair (β₂-Nf/Nf nf₁ _ _) (β₂-Nf/Nf nf₂ _ _)
  β₂-Nf/Nf uniq _ _ = refl

  -- this is the "big" inductive lemma for IDR
  IDR-lem : ∀{Γ τ Δ} →
    (n : NormalForm Γ τ)
    (ast : Embedded Γ τ n Δ) →
    Nf/Nf (SHIFT ⟨ ast ⟩) ∣ ast ∣ ≡ n
  IDR-lem {τ = ↑ x} _ root = refl
  IDR-lem {τ = ↑ x} n (left ast nf) = β₁-Ne/Nf ⟨ ast ⟩ ∣ ast ∣ nf ∙  IDR-lem n ast
  IDR-lem {τ = ↑ x} n (right nf ast) = β₂-Ne/Nf ⟨ ast ⟩ nf ∣ ast ∣ ∙ IDR-lem n ast
  IDR-lem {τ = τ₁ × τ₂} (pair n₁ n₂) root = cong₂ pair (IDR-lem n₁ $ left root n₂) (IDR-lem n₂ $ right n₁ root)
  IDR-lem {τ = τ₁ × τ₂} (pair n₁ n₂) (left ast nf) = cong₂ pair
    (congS (λ x → Nf/Nf x $ pair ∣ ast ∣ nf) (SHIFT-∘proj₁) ∙ β₁-Nf/Nf (SHIFT _) ∣ ast ∣ nf)
    (congS (λ x → Nf/Nf x $ pair ∣ ast ∣ nf) (SHIFT-∘proj₁) ∙ β₁-Nf/Nf (SHIFT _) ∣ ast ∣ nf)
    ∙ IDR-lem (pair n₁ n₂) ast
  IDR-lem {τ = τ₁ × τ₂} (pair n₁ n₂) (right nf ast) = cong₂ pair
    (congS (λ x → Nf/Nf x $ pair nf ∣ ast ∣) (SHIFT-∘proj₂) ∙ β₂-Nf/Nf (SHIFT _) nf ∣ ast ∣)
    (congS (λ x → Nf/Nf x $ pair nf ∣ ast ∣) (SHIFT-∘proj₂) ∙ β₂-Nf/Nf (SHIFT _) nf ∣ ast ∣)
    ∙ IDR-lem (pair n₁ n₂) ast
  IDR-lem {τ = ⊤} uniq _ = refl

  IDR : ∀{Γ τ} (n : NormalForm Γ τ) → Nf/Nf ID n ≡ n
  IDR n = IDR-lem n root

  Nf/Nf-PROJ₁ : ∀{Γ Δ τ₁ τ₂} (n₁ : NormalForm Δ (τ₁ × τ₂)) (n₂ : NormalForm Γ Δ) →
    Nf/Nf (PROJ₁ n₁) n₂ ≡ PROJ₁ (Nf/Nf n₁ n₂)
  Nf/Nf-PROJ₁ (pair _ _) _ = refl

  Nf/Nf-PROJ₂ : ∀{Γ Δ τ₁ τ₂} (n₁ : NormalForm Δ (τ₁ × τ₂)) (n₂ : NormalForm Γ Δ) →
    Nf/Nf (PROJ₂ n₁) n₂ ≡ PROJ₂ (Nf/Nf n₁ n₂)
  Nf/Nf-PROJ₂ (pair _ _) _ = refl

  ASSOC-Nf/Nf/Nf : ∀{Γ Δ Θ τ} →
    (n₃ : NormalForm Θ τ)
    (n₂ : NormalForm Δ Θ)
    (n₁ : NormalForm Γ Δ) →
    Nf/Nf n₃ (Nf/Nf n₂ n₁) ≡ Nf/Nf (Nf/Nf n₃ n₂) n₁
  ASSOC-Ne/Nf/Nf : ∀{Γ Δ Θ τ} →
    (n₃ : NeutralTerm Θ τ)
    (n₂ : NormalForm Δ Θ)
    (n₁ : NormalForm Γ Δ) →
    Ne/Nf n₃ (Nf/Nf n₂ n₁) ≡ Nf/Nf (Ne/Nf n₃ n₂) n₁

  ASSOC-Nf/Nf/Nf (shift ne) = ASSOC-Ne/Nf/Nf ne
  ASSOC-Nf/Nf/Nf (pair n₃ n₄) n₂ n₁ = cong₂ pair (ASSOC-Nf/Nf/Nf n₃ n₂ n₁) (ASSOC-Nf/Nf/Nf n₄ n₂ n₁)
  ASSOC-Nf/Nf/Nf uniq _ _ = refl

  ASSOC-Ne/Nf/Nf var _ _ = refl
  ASSOC-Ne/Nf/Nf (proj₁ n₃) n₂ n₁ = congS PROJ₁ (ASSOC-Ne/Nf/Nf n₃ n₂ n₁) ∙ sym (Nf/Nf-PROJ₁ (Ne/Nf n₃ n₂) n₁)
  ASSOC-Ne/Nf/Nf (proj₂ n₃) n₂ n₁ = congS PROJ₂ (ASSOC-Ne/Nf/Nf n₃ n₂ n₁) ∙ sym (Nf/Nf-PROJ₂ (Ne/Nf n₃ n₂) n₁)
  ASSOC-Ne/Nf/Nf (symb f nf) n₂ n₁ = congS (shift ∘S symb f) (ASSOC-Nf/Nf/Nf nf n₂ n₁)

  _⋆⋆_ : ∀{Γ Δ τ} → ∥ NormalForm Γ Δ ∥₂ → ∥ NormalForm Δ τ ∥₂ → ∥ NormalForm Γ τ ∥₂
  _⋆⋆_ = rec2 isSetSetTrunc (λ n m → ∣ Nf/Nf m n ∣₂)

  ∣IDL∣₂ : ∀{Γ τ} → (n : ∥ NormalForm Γ τ ∥₂) → (∣ ID ∣₂ ⋆⋆ n) ≡ n
  ∣IDL∣₂ ∣ n ∣₂ = congS ∣_∣₂ (IDL n)
  ∣IDL∣₂ (squash₂ n m p q i j) k = squash₂ _ _ (congS (λ x → ∣IDL∣₂ x k) p) ((congS (λ x → ∣IDL∣₂ x k) q)) i j

  ∣IDR∣₂ : ∀{Γ τ} → (n : ∥ NormalForm Γ τ ∥₂) → (n ⋆⋆ ∣ ID ∣₂) ≡ n
  ∣IDR∣₂ ∣ n ∣₂ = congS ∣_∣₂ (IDR n)
  ∣IDR∣₂ (squash₂ n m p q i j) k = squash₂ _ _ (congS (λ x → ∣IDR∣₂ x k) p) ((congS (λ x → ∣IDR∣₂ x k) q)) i j

  ∣ASSOC∣₂ : ∀{Γ Δ Θ τ} →
    (n₃ : ∥ NormalForm Θ τ ∥₂)
    (n₂ : ∥ NormalForm Δ Θ ∥₂)
    (n₁ : ∥ NormalForm Γ Δ ∥₂) →
    ((n₁ ⋆⋆ n₂) ⋆⋆ n₃) ≡ (n₁ ⋆⋆ (n₂ ⋆⋆ n₃))
  ∣ASSOC∣₂ ∣ n₃ ∣₂ ∣ n₂ ∣₂ ∣ n₁ ∣₂ = cong ∣_∣₂ (ASSOC-Nf/Nf/Nf n₃ n₂ n₁)
  ∣ASSOC∣₂ ∣ n₃ ∣₂ ∣ n₂ ∣₂ (squash₂ n m p q i j) k = squash₂ _ _ (congS (λ x → ∣ASSOC∣₂ ∣ n₃ ∣₂ ∣ n₂ ∣₂ x k) p) ((congS (λ x → ∣ASSOC∣₂ ∣ n₃ ∣₂ ∣ n₂ ∣₂ x k) q)) i j
  ∣ASSOC∣₂ ∣ n₃ ∣₂ (squash₂ n m p q i j) ∣ n₁ ∣₂ k = squash₂ _ _ (congS (λ x → ∣ASSOC∣₂ ∣ n₃ ∣₂ x ∣ n₁ ∣₂ k) p) (congS (λ x → ∣ASSOC∣₂ ∣ n₃ ∣₂ x ∣ n₁ ∣₂ k) q) i j
  ∣ASSOC∣₂ ∣ n₃ ∣₂ (squash₂ n m p q i j) (squash₂ n' m' p' q' i' j') k = squash₂ {!∣ASSOC∣₂ ∣ n₃ ∣₂ (p k) (squash₂ n' m' p' q' i' j')!} {!!} {!!} {!!} {!!} {!!} --k = squash₂ (∣ASSOC∣₂ ∣ n₃ ∣₂ n n' k) (∣ASSOC∣₂ ∣ n₃ ∣₂ m m' k) (cong₂ (λ x y → ∣ASSOC∣₂ ∣ n₃ ∣₂ x y k) p p') ((cong₂ (λ x y → ∣ASSOC∣₂ ∣ n₃ ∣₂ x y k) q q')) {!!} {!!}
  ∣ASSOC∣₂ (squash₂ n m p q i j) ∣ n₂ ∣₂ ∣ n₁ ∣₂ k = squash₂ _ _ (congS (λ x → ∣ASSOC∣₂ x ∣ n₂ ∣₂ ∣ n₁ ∣₂ k) p) (congS (λ x → ∣ASSOC∣₂ x ∣ n₂ ∣₂ ∣ n₁ ∣₂ k) q) i j
  --∣ASSOC∣₂ (squash₂ n₃ n₄ p q i j) n₂ n₁ = {!!}

  |Nf| : Category _ _
  |Nf| .ob = Q.Ob
  |Nf| .Hom[_,_] Γ τ = ∥ NormalForm Γ τ ∥₂ --NormalForm
  |Nf| .id = ∣ ID ∣₂ --ID
  |Nf| ._⋆_ = _⋆⋆_ --Nf/Nf m n
  |Nf| .⋆IdL = ∣IDL∣₂
  |Nf| .⋆IdR = ∣IDR∣₂ --IDR
  |Nf| .⋆Assoc n₁ n₂ n₃ = ∣ASSOC∣₂ n₃ n₂ n₁ --ASSOC-Nf/Nf/Nf n₃ n₂ n₁
  |Nf| .isSetHom = isSetSetTrunc

  ----Nf : CartesianCategory {!!} {!!}
  ----Nf .fst = |Nf|
  ----Nf .snd .fst = {!!}
  ----Nf .snd .snd = {!!}
