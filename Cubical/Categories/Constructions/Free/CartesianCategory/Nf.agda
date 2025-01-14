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

  -- two different ASTs for contexts, by induction on the domain and codomain
  data Contains (τ : Q.Ob) : (Γ : Q.Ob) → Type ℓq where
    root : Contains τ τ
    left : ∀{Γ Δ} → Contains τ Γ → Contains τ (Γ × Δ)
    right : ∀{Γ Δ} → Contains τ Δ → Contains τ (Γ × Δ)
  data Contains' (Γ : Q.Ob) : (τ : Q.Ob) → Type ℓq where
    root : Contains' Γ Γ
    left : ∀{τ₁ τ₂} → Contains' Γ (τ₁ × τ₂) → Contains' Γ τ₁
    right : ∀{τ₁ τ₂} → Contains' Γ (τ₁ × τ₂) → Contains' Γ τ₂
  data Embedded Γ τ (n : NormalForm Γ τ) : Q.Ob → Type (ℓ-max ℓq ℓq') where
    root : Embedded Γ τ n τ
    left : ∀{τ' τ''} → Embedded Γ τ n τ' → NormalForm Γ τ'' → Embedded Γ τ n (τ' × τ'')
    right : ∀{τ' τ''} → NormalForm Γ τ' → Embedded Γ τ n τ'' → Embedded Γ τ n (τ' × τ'')

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

  Contains'→NeutralTerm : ∀{Γ τ} → Contains' Γ τ → NeutralTerm Γ τ
  Contains'→NeutralTerm root = var
  Contains'→NeutralTerm (left ast) = proj₁ (Contains'→NeutralTerm ast)
  Contains'→NeutralTerm (right ast) = proj₂ (Contains'→NeutralTerm ast)

  Contains'→HOAS? : ∀{Γ Δ τ} → Contains' Δ τ → NormalForm Γ Δ → NormalForm Γ τ
  Contains'→HOAS? root = idfun _
  Contains'→HOAS? (left ast) = PROJ₁ ∘S (Contains'→HOAS? ast)
  Contains'→HOAS? (right ast) = PROJ₂ ∘S (Contains'→HOAS? ast)

  Contains→NeutralTerm : ∀{Γ τ} → Contains τ Γ → NeutralTerm Γ τ
  Contains→NeutralTerm root = var
  Contains→NeutralTerm (left ast) = Ne/Ne (Contains→NeutralTerm ast) (proj₁ var)
  Contains→NeutralTerm (right ast) = Ne/Ne (Contains→NeutralTerm ast) (proj₂ var)

  Contains→HOAS? : ∀{Γ Δ τ} → Contains τ Δ → NormalForm Γ Δ → NormalForm Γ τ
  Contains→HOAS? root = idfun _
  Contains→HOAS? (left ast) = Contains→HOAS? ast ∘S PROJ₁
  Contains→HOAS? (right ast) = Contains→HOAS? ast ∘S PROJ₂

  ∘proj₁ : ∀{Γ Δ τ} → NeutralTerm Γ τ → NeutralTerm (Γ × Δ) τ
  ∘PROJ₁ : ∀{Γ Δ τ} → NormalForm Γ τ → NormalForm (Γ × Δ) τ
  ∘proj₁ var = proj₁ var
  ∘proj₁ (proj₁ n) = proj₁ (∘proj₁ n)
  ∘proj₁ (proj₂ n) = proj₂ (∘proj₁ n)
  ∘proj₁ (symb f x) = symb f (∘PROJ₁ x)
  ∘PROJ₁ (shift x) = shift (∘proj₁ x)
  ∘PROJ₁ (pair n n₁) = pair (∘PROJ₁ n) (∘PROJ₁ n₁)
  ∘PROJ₁ uniq = uniq
  ∘proj₂ : ∀{Γ Δ τ} → NeutralTerm Δ τ → NeutralTerm (Γ × Δ) τ
  ∘PROJ₂ : ∀{Γ Δ τ} → NormalForm Δ τ → NormalForm (Γ × Δ) τ
  ∘proj₂ var = proj₂ var
  ∘proj₂ (proj₁ n) = proj₁ (∘proj₂ n)
  ∘proj₂ (proj₂ n) = proj₂ (∘proj₂ n)
  ∘proj₂ (symb f x) = symb f (∘PROJ₂ x)
  ∘PROJ₂ (shift x) = shift (∘proj₂ x)
  ∘PROJ₂ (pair n n₁) = pair (∘PROJ₂ n) (∘PROJ₂ n₁)
  ∘PROJ₂ uniq = uniq

  Embedded→NeutralTerm : ∀{Γ τ n Δ} →
    Embedded Γ τ n Δ → NeutralTerm Δ τ
  Embedded→NeutralTerm root = var
  Embedded→NeutralTerm (left e _) = ∘proj₁ (Embedded→NeutralTerm e)
  Embedded→NeutralTerm (right _ e) = ∘proj₂ (Embedded→NeutralTerm e)

  |Embedded| : ∀{Γ τ n Δ} →
    Embedded Γ τ n Δ → NormalForm Γ Δ
  |Embedded| {n = n} root = n
  |Embedded| (left e x) = pair (|Embedded| e) x
  |Embedded| (right x e) = pair x (|Embedded| e)

  -- NOTE: same as ID', but just to be more clear
  ID'' : ∀{τ} → NormalForm τ τ
  ID'' = SHIFT (Contains'→NeutralTerm root)

  --MEGA : ∀{Γ Δ τ} → (n : NormalForm Γ Δ)
  --  (ast : Contains τ Δ) →
  --  Nf/Nf (SHIFT (Contains'→NeutralTerm ast)) n ≡ Contains'→HOAS? ast n
  --MEGA {τ = τ} n ast = ?
  MEGA : ∀{Γ τ Δ} →
    (n : NormalForm Γ τ)
    (ast : Embedded Γ τ n Δ) →
    Nf/Nf (SHIFT (Embedded→NeutralTerm ast)) (|Embedded| ast) ≡ n
  MEGA {τ = ↑ x} n root = refl
  MEGA {τ = ↑ x} (shift x₂) (left ast x₁) = {!!} ∙ MEGA (shift x₂) ast
  MEGA {τ = ↑ x} n (right x₁ ast) = {!!}
  MEGA {τ = τ₁ × τ₂} n ast = {!!}
  MEGA {τ = ⊤} n ast = {!!}

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
