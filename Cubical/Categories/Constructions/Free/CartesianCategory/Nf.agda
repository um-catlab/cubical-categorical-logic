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

  -- two different ASTs for contexts, by induction on the domain and codomain
  data Contains (τ : Q.Ob) : (Γ : Q.Ob) → Type ℓq where
    root : Contains τ τ
    left : ∀{Γ Δ} → Contains τ Γ → Contains τ (Γ × Δ)
    right : ∀{Γ Δ} → Contains τ Δ → Contains τ (Γ × Δ)
  data Contains' (Γ : Q.Ob) : (τ : Q.Ob) → Type ℓq where
    root : Contains' Γ Γ
    left : ∀{τ₁ τ₂} → Contains' Γ (τ₁ × τ₂) → Contains' Γ τ₁
    right : ∀{τ₁ τ₂} → Contains' Γ (τ₁ × τ₂) → Contains' Γ τ₂

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

  -- [[deprecated]]
  UNIV : ∀{Γ} (τ : Q.Ob) → Contains τ Γ → NormalForm Γ τ
  UNIV (↑ x) root = shift var
  UNIV (τ₁ × τ₂) root = pair (UNIV _ (left root)) (UNIV _ (right root))
  UNIV ⊤ _ = uniq
  UNIV _ (left AST) = Nf/Ne (UNIV _ AST) (proj₁ var)
  UNIV _ (right AST) = Nf/Ne (UNIV _ AST) (proj₂ var)

  -- [[deprecated]]
  ID : ∀{τ} → NormalForm τ τ
  ID = UNIV _ root

  ID' : ∀{τ} → NormalForm τ τ
  ID' = SHIFT var

  IDLNe : ∀{Γ τ} (n : NeutralTerm Γ τ) → (Ne/Nf n ID') ≡ SHIFT n
  IDL : ∀{Γ τ} (n : NormalForm Γ τ) → Nf/Nf n ID' ≡ n
  IDL (shift x) = IDLNe x
  IDL (pair n n₁) = cong₂ pair (IDL n) (IDL n₁)
  IDL uniq = refl
  IDLNe var = refl
  IDLNe (proj₁ n) = congS PROJ₁ (IDLNe n)
  IDLNe (proj₂ n) = congS PROJ₂ (IDLNe n)
  IDLNe (symb f x) = congS (λ z → shift (symb f z)) (IDL x)
  --IDLNe (isSetNe n n₁ x y i i₁) = {!!}

  --∀{Γ τ} → (n : NormalForm Γ τ) (n in pair) → Nf/Nf (SHIFT ?) (?) ≡ n
  IDR : ∀{Γ τ} (n : NormalForm Γ τ) → Nf/Nf ID' n ≡ n
  PPR₁ : ∀{Γ τ₁ τ₂} (n₁ : NormalForm Γ τ₁) (n₂ : NormalForm Γ τ₂) → Nf/Nf (SHIFT (proj₁ var)) (pair n₁ n₂) ≡ n₁
  PPR₂ : ∀{Γ τ₁ τ₂} (n₁ : NormalForm Γ τ₁) (n₂ : NormalForm Γ τ₂) → Nf/Nf (SHIFT (proj₂ var)) (pair n₁ n₂) ≡ n₂
  IDR (shift x) = refl
  IDR (pair n n₁) = cong₂ pair {!!} {!!}
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
