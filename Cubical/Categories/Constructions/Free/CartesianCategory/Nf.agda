module Cubical.Categories.Constructions.Free.CartesianCategory.Nf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver

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
    --isSetNe : ∀{Γ τ} → isSet (NeutralTerm Γ τ)
  data NormalForm where
    -- shift only at ground types to enforce η-long normal forms
    shift : ∀{Γ τ} → NeutralTerm Γ (↑ τ) → NormalForm Γ (↑ τ)
    pair : ∀{Γ τ₁ τ₂} → NormalForm Γ τ₁ → NormalForm Γ τ₂ → NormalForm Γ (τ₁ × τ₂)
    uniq : ∀{Γ} → NormalForm Γ ⊤
    --isSetNf : ∀{Γ τ} → isSet (NormalForm Γ τ)

  -- NOTE: something of this type should always exist, but how to define it so it behaves well?
  -- Desiderata:
  -- - SHIFT ≡ shift, at base types
  -- this is the "type directed" shift
  SHIFT : ∀{Γ τ} → NeutralTerm Γ τ → NormalForm Γ τ
  SHIFT {Γ} {τ = ↑ _} = shift
  SHIFT {Γ} {τ = τ₁ × τ₂} n = pair (SHIFT (proj₁ n)) (SHIFT (proj₂ n))
  SHIFT {Γ} {τ = ⊤} n = uniq
  -- there's also a constructor-directed (syntax directed?) shift, but it doesn't obviously have any nice properties?

  -- TODO: do we *really* need to use this?
  PROJ₁ : ∀{Γ τ₁ τ₂} → NormalForm Γ (τ₁ × τ₂) → NormalForm Γ τ₁
  PROJ₁ (pair n₁ _) = n₁
  --PROJ₁ (isSetNf n m p q i j) = isSetNf (PROJ₁ n) (PROJ₁ m) (congS PROJ₁ p) (congS PROJ₁ q) i j
  PROJ₂ : ∀{Γ τ₁ τ₂} → NormalForm Γ (τ₁ × τ₂) → NormalForm Γ τ₂
  PROJ₂ (pair _ n₂) = n₂
  --PROJ₂ (isSetNf n m p q i j) = isSetNf (PROJ₂ n) (PROJ₂ m) (congS PROJ₂ p) (congS PROJ₂ q) i j

  --ETA : ∀{Γ τ₁ τ₂} (n : NormalForm Γ (τ₁ × τ₂)) → pair (PROJ₁ n) (PROJ₂ n) ≡ n
  --ETA (pair n n₁) = refl
  ETA : ∀{Γ τ₁ τ₂} (n : NormalForm Γ (τ₁ × τ₂)) → n ≡ pair (PROJ₁ n) (PROJ₂ n)
  ETA (pair n n₁) = refl
  --ETA (isSetNf n n₁ x y i i₁) = {!!}

  ETA! : ∀{Γ} (n : NormalForm Γ ⊤) → n ≡ uniq
  ETA! uniq = refl

  ETA↑ : ∀{Γ x} (n : NormalForm Γ (↑ x)) → Σ (NeutralTerm Γ (↑ x)) λ ne → n ≡ shift ne
  ETA↑ (shift x) = x , refl

  Nf/Nf : ∀{Γ Δ τ} → NormalForm Δ τ → NormalForm Γ Δ → NormalForm Γ τ
  Ne/Nf : ∀{Γ Δ τ} → NeutralTerm Δ τ → NormalForm Γ Δ → NormalForm Γ τ
  Nf/Ne : ∀{Γ Δ τ} → NormalForm Δ τ → NeutralTerm Γ Δ → NormalForm Γ τ
  Ne/Ne : ∀{Γ Δ τ} → NeutralTerm Δ τ → NeutralTerm Γ Δ → NeutralTerm Γ τ
  Nf/Nf (shift x) x₁ = Ne/Nf x x₁
  Nf/Nf (pair x x₂) x₁ = pair (Nf/Nf x x₁) (Nf/Nf x₂ x₁)
  Nf/Nf uniq x₁ = uniq
  --Nf/Nf (isSetNf x x₂ x₃ y i i₁) x₁ = isSetNf (Nf/Nf x x₁) (Nf/Nf x₂ x₁) (cong₂ Nf/Nf x₃ refl) (cong₂ Nf/Nf y refl) i i₁
  Ne/Nf var x₁ = x₁
  Ne/Nf (proj₁ x) x₁ = PROJ₁ (Ne/Nf x x₁)
  Ne/Nf (proj₂ x) x₁ = PROJ₂ (Ne/Nf x x₁)
  Ne/Nf (symb f x) x₁ = shift (symb f (Nf/Nf x x₁))
  --Ne/Nf (isSetNe x x₂ x₃ y i i₁) x₁ = isSetNf (Ne/Nf x x₁) (Ne/Nf x₂ x₁) (cong₂ Ne/Nf x₃ refl) (cong₂ Ne/Nf y refl) i i₁
  Nf/Ne (shift x) x₁ = shift (Ne/Ne x x₁)
  Nf/Ne (pair x x₂) x₁ = pair (Nf/Ne x x₁) (Nf/Ne x₂ x₁)
  Nf/Ne uniq x₁ = uniq
  --Nf/Ne (isSetNf x x₂ x₃ y i i₁) x₁ = isSetNf (Nf/Ne x x₁) (Nf/Ne x₂ x₁) (cong₂ Nf/Ne x₃ refl) (cong₂ Nf/Ne y refl) i i₁
  Ne/Ne var x₁ = x₁
  Ne/Ne (proj₁ x) x₁ = proj₁ (Ne/Ne x x₁)
  Ne/Ne (proj₂ x) x₁ = proj₂ (Ne/Ne x x₁)
  Ne/Ne (symb f x) x₁ = symb f (Nf/Ne x x₁)
  --Ne/Ne (isSetNe x x₂ x₃ y i i₁) x₁ = isSetNe (Ne/Ne x x₁) (Ne/Ne x₂ x₁) (cong₂ Ne/Ne x₃ refl) (cong₂ Ne/Ne y refl) i i₁

  data Embedded Γ τ (n : NormalForm Γ τ) : Q.Ob → Type (ℓ-max ℓq ℓq') where
    root : Embedded Γ τ n τ
    left : ∀{τ' τ''} → Embedded Γ τ n τ' → NormalForm Γ τ'' → Embedded Γ τ n (τ' × τ'')
    right : ∀{τ' τ''} → NormalForm Γ τ' → Embedded Γ τ n τ'' → Embedded Γ τ n (τ' × τ'')

  ID' : ∀{τ} → NormalForm τ τ
  ID' = SHIFT var

  IDL : ∀{Γ τ} (n : NormalForm Γ τ) → Nf/Nf n ID' ≡ n
  IDLNe : ∀{Γ τ} (n : NeutralTerm Γ τ) → (Ne/Nf n ID') ≡ SHIFT n
  IDL (shift x) = IDLNe x
  IDL (pair n n₁) = cong₂ pair (IDL n) (IDL n₁)
  IDL uniq = refl
  IDLNe var = refl
  IDLNe (proj₁ n) = congS PROJ₁ (IDLNe n)
  IDLNe (proj₂ n) = congS PROJ₂ (IDLNe n)
  IDLNe (symb f x) = congS (λ z → shift (symb f z)) (IDL x)
  --IDLNe (isSetNe n n₁ x y i i₁) = {!!}

  _∘proj₁ : ∀{Γ Δ τ} → NeutralTerm Γ τ → NeutralTerm (Γ × Δ) τ
  _∘PROJ₁ : ∀{Γ Δ τ} → NormalForm Γ τ → NormalForm (Γ × Δ) τ
  var ∘proj₁ = proj₁ var
  (proj₁ n) ∘proj₁ = proj₁ (n ∘proj₁)
  (proj₂ n) ∘proj₁ = proj₂ (n ∘proj₁)
  (symb f x) ∘proj₁ = symb f (x ∘PROJ₁)
  (shift x) ∘PROJ₁ = shift (x ∘proj₁)
  (pair n₁ n₂) ∘PROJ₁ = pair (n₁ ∘PROJ₁) (n₂ ∘PROJ₁)
  uniq ∘PROJ₁ = uniq

  _∘proj₂ : ∀{Γ Δ τ} → NeutralTerm Δ τ → NeutralTerm (Γ × Δ) τ
  _∘PROJ₂ : ∀{Γ Δ τ} → NormalForm Δ τ → NormalForm (Γ × Δ) τ
  _∘proj₂ var = proj₂ var
  _∘proj₂ (proj₁ n) = proj₁ (n ∘proj₂)
  _∘proj₂ (proj₂ n) = proj₂ (n ∘proj₂)
  _∘proj₂ (symb f x) = symb f (x ∘PROJ₂)
  _∘PROJ₂ (shift x) = shift (x ∘proj₂)
  _∘PROJ₂ (pair n n₁) = pair (n ∘PROJ₂) (n₁ ∘PROJ₂)
  _∘PROJ₂ uniq = uniq

  ⟨_⟩ : ∀{Γ τ n Δ} →
    Embedded Γ τ n Δ → NeutralTerm Δ τ
  ⟨ root ⟩ = var
  ⟨ left e _ ⟩ = ⟨ e ⟩ ∘proj₁
  ⟨ right _ e ⟩ = ⟨ e ⟩ ∘proj₂

  ∣_∣ : ∀{Γ τ n Δ} →
    Embedded Γ τ n Δ → NormalForm Γ Δ
  ∣_∣ {n = n} root = n
  ∣_∣ (left e x) = pair (∣ e ∣) x
  ∣_∣ (right x e) = pair x (∣ e ∣)

  β₁ : ∀{Γ τ₁ τ₂ τ₃} →
    (ne : NeutralTerm τ₁ τ₃) →
    (nf₁ : NormalForm Γ τ₁) →
    (nf₂ : NormalForm Γ τ₂) →
    Ne/Nf (ne ∘proj₁) (pair nf₁ nf₂) ≡ Ne/Nf ne nf₁
  β₁-Nf : ∀{Γ τ₁ τ₂ τ₃} →
    (n : NormalForm τ₁ τ₃) →
    (nf₁ : NormalForm Γ τ₁) →
    (nf₂ : NormalForm Γ τ₂) →
    Nf/Nf (n ∘PROJ₁) (pair nf₁ nf₂) ≡ Nf/Nf n nf₁
  β₁ var nf₁ nf₂ = refl
  β₁ (proj₁ ne) nf₁ nf₂ = congS PROJ₁ (β₁ ne nf₁ nf₂)
  β₁ (proj₂ ne) nf₁ nf₂ = congS PROJ₂ (β₁ ne nf₁ nf₂)
  β₁ (symb f x) nf₁ nf₂ = congS shift (congS (λ z → symb f z) (β₁-Nf x _ _))
  β₁-Nf (shift x) nf₁ nf₂ = β₁ x _ _
  β₁-Nf (pair n n₁) nf₁ nf₂ = cong₂ pair (β₁-Nf n _ _) (β₁-Nf n₁ _ _)
  β₁-Nf uniq nf₁ nf₂ = refl

  PROJ₁-Embedded : ∀{Γ τ₁ τ₂ n₁ n₂ Δ} →
    Embedded Γ (τ₁ × τ₂) (pair n₁ n₂) Δ →
    Embedded Γ τ₁ n₁ Δ
  PROJ₁-Embedded {n₂ = n₂} root = left root n₂
  PROJ₁-Embedded (left ast x) = left (PROJ₁-Embedded ast) x
  PROJ₁-Embedded (right x ast) = right x (PROJ₁-Embedded ast)

  MEGA : ∀{Γ τ Δ} →
    (n : NormalForm Γ τ)
    (ast : Embedded Γ τ n Δ) →
    Nf/Nf (SHIFT ⟨ ast ⟩) ∣ ast ∣ ≡ n
  MEGA {τ = ↑ x} _ root = refl
  MEGA {τ = ↑ x} n (left ast x₁) = β₁ ⟨ ast ⟩ ∣ ast ∣ x₁ ∙ MEGA n ast
  MEGA {τ = ↑ x} n (right x₁ ast) = {!!}
  MEGA {τ = τ₁ × τ₂} (pair n₁ n₂) root = cong₂ pair (MEGA n₁ (left root n₂)) (MEGA n₂ (right n₁ root))
  MEGA {τ = τ₁ × τ₂} (pair n₁ n₂) (left ast x) = cong₂ pair ({!!} ∙ MEGA n₁ (left (PROJ₁-Embedded ast) x)) (MEGA n₂ {!!})
  MEGA {τ = τ₁ × τ₂} n (right x ast) = {!!}
  MEGA {τ = ⊤} uniq _ = refl

  IDR : ∀{Γ τ} (n : NormalForm Γ τ) → Nf/Nf ID' n ≡ n
  PPR₁ : ∀{Γ τ₁ τ₂} (n₁ : NormalForm Γ τ₁) (n₂ : NormalForm Γ τ₂) → Nf/Nf (SHIFT (proj₁ var)) (pair n₁ n₂) ≡ n₁
  PPR₂ : ∀{Γ τ₁ τ₂} (n₁ : NormalForm Γ τ₁) (n₂ : NormalForm Γ τ₂) → Nf/Nf (SHIFT (proj₂ var)) (pair n₁ n₂) ≡ n₂
  IDR (shift x) = refl
  IDR (pair n₁ n₂) = cong₂ pair {!MEGA (pair n₁ n₂) (left root)!} {!!}
  IDR uniq = refl
  PPR₁ {τ₁ = ↑ x} _ _ = refl
  PPR₁ {τ₁ = τ₁ × τ₂} (pair n₁₁ n₁₂) n₂ = cong₂ pair {!PPR₁ ? ?!} {!!}
  PPR₁ {τ₁ = ⊤} uniq _ = refl
  PPR₂ = {!!}

  |Nf| : Category {!!} {!!}
  |Nf| .ob = Q.Ob
  |Nf| .Hom[_,_] = NormalForm
  |Nf| .id = ID'
  |Nf| ._⋆_ n m = Nf/Nf m n
  |Nf| .⋆IdL n = IDL n
  |Nf| .⋆IdR = {!!}
  |Nf| .⋆Assoc = {!!}
  |Nf| .isSetHom = {!!} --isSetNf
  --Nf : CartesianCategory {!!} {!!}
  --Nf .fst = |Nf|
  --Nf .snd .fst = {!!}
  --Nf .snd .snd = {!!}
