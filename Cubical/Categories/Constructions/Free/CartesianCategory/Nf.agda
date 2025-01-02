module Cubical.Categories.Constructions.Free.CartesianCategory.Nf where

open import Cubical.Foundations.Prelude

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
    -- pair?
    --isSetNe : ∀{Γ τ} → isSet (NeutralTerm Γ τ)
  data NormalForm where
    shift : ∀{Γ τ} → NeutralTerm Γ (↑ τ) → NormalForm Γ (↑ τ)
    pair : ∀{Γ τ₁ τ₂} → NormalForm Γ τ₁ → NormalForm Γ τ₂ → NormalForm Γ (τ₁ × τ₂)
    uniq : ∀{Γ} → NormalForm Γ ⊤
    --isSetNf : ∀{Γ τ} → isSet (NormalForm Γ τ)
  data Contains (τ : Q.Ob) : (Γ : Q.Ob) → Type ℓq where
    root : Contains τ τ
    left : ∀{Γ Δ} → Contains τ Γ → Contains τ (Γ × Δ)
    right : ∀{Γ Δ} → Contains τ Δ → Contains τ (Γ × Δ)
  data Contains' (Γ : Q.Ob) : (τ : Q.Ob) → Type ℓq where
    root : Contains' Γ Γ
    left : ∀{τ₁ τ₂} → Contains' Γ (τ₁ × τ₂) → Contains' Γ τ₁
    right : ∀{τ₁ τ₂} → Contains' Γ (τ₁ × τ₂) → Contains' Γ τ₂
  --foo : NormalForm
  -- id
  --SHIFT : ∀{Γ τ} → NeutralTerm Γ τ → NormalForm Γ τ
  --SHIFT {Γ} {τ = ↑ _} = shift
  --SHIFT {Γ} {τ = τ × τ₁} x = pair (SHIFT {!!}) {!!}
  --SHIFT {Γ} {τ = ⊤} x = {!!}
  --isNormal :
  --nt : (Γ : Q.Ob) → Q.Ob
  --nt (↑ x) = ↑ x
  --nt (x × x₁) = nt x × nt x₁
  --nt ⊤ = ⊤
  PROJ₁ : ∀{Γ τ₁ τ₂} → NormalForm Γ (τ₁ × τ₂) → NormalForm Γ τ₁
  PROJ₁ (pair n _) = n
  --PROJ₁ (isSetNf n m p q i j) = isSetNf (PROJ₁ n) (PROJ₁ m) (congS PROJ₁ p) (congS PROJ₁ q) i j
  PROJ₂ : ∀{Γ τ₁ τ₂} → NormalForm Γ (τ₁ × τ₂) → NormalForm Γ τ₂
  PROJ₂ (pair _ m) = m
  --PROJ₂ (isSetNf n m p q i j) = isSetNf (PROJ₂ n) (PROJ₂ m) (congS PROJ₂ p) (congS PROJ₂ q) i j
  --ETA : ∀{Γ τ₁ τ₂} (n : NormalForm Γ (τ₁ × τ₂)) → pair (PROJ₁ n) (PROJ₂ n) ≡ n
  --ETA (pair n n₁) = refl
  ETA : ∀{Γ τ₁ τ₂} (n : NormalForm Γ (τ₁ × τ₂)) → n ≡ pair (PROJ₁ n) (PROJ₂ n)
  ETA (pair n n₁) = refl
  --ETA (isSetNf n n₁ x y i i₁) = {!!}
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
  UNIVNe : ∀{Γ τ} → Contains' Γ τ → NeutralTerm Γ τ
  UNIVNe root = var
  UNIVNe (left ast) = proj₁ (UNIVNe ast)
  UNIVNe (right ast) = proj₂ (UNIVNe ast)
  --UNIVNf : ∀{Γ} (τ : Q.Ob) → Contains' Γ τ → NormalForm Γ τ
  --UNIVNf (↑ x) root = shift var
  --UNIVNf (↑ x) (left AST) = PROJ₁ (UNIVNf _ AST)
  --UNIVNf (↑ x) (right AST) = PROJ₂ (UNIVNf _ AST)
  --UNIVNf (τ₁ × τ₂) root = {!!} --pair (UNIVNf τ₁ (left root)) {!!}
  --UNIVNf (τ × τ₁) (left ast) = {!!}
  --UNIVNf (τ × τ₁) (right ast) = {!!}
  --UNIVNf ⊤ ast = {!!}
  UNIV : ∀{Γ} (τ : Q.Ob) → Contains τ Γ → NormalForm Γ τ
  UNIV (↑ x) root = shift var
  UNIV (↑ x) (left AST) = Nf/Ne (UNIV _ AST) (proj₁ var)
  UNIV (↑ x) (right AST) = Nf/Ne (UNIV _ AST) (proj₂ var)
  UNIV (τ₁ × τ₂) root = pair (UNIV τ₁ (left root)) (UNIV τ₂ (right root))
  UNIV (τ₁ × τ₂) (left AST) = Nf/Ne (UNIV _ AST) (proj₁ var)
  UNIV (τ₁ × τ₂) (right AST) = Nf/Ne (UNIV _ AST) (proj₂ var)
  UNIV ⊤ _ = uniq
  ID : ∀{τ} → NormalForm τ τ
  ID = UNIV _ root
  PI₁ : ∀{τ₁ τ₂} → NormalForm (τ₁ × τ₂) τ₁
  PI₁ = UNIV _ (left root)
  PI₂ : ∀{τ₁ τ₂} → NormalForm (τ₁ × τ₂) τ₂
  PI₂ = UNIV _ (right root)
  SHIFT' : ∀{Γ τ} → NeutralTerm Γ τ → NormalForm Γ τ
  SHIFT' var = ID
  SHIFT' (proj₁ n) = PROJ₁ (SHIFT' n)
  SHIFT' (proj₂ n) = PROJ₂ (SHIFT' n)
  SHIFT' (symb f x) = shift (symb f x)
  --SHIFT' (isSetNe n n₁ x y i i₁) = isSetNf (SHIFT' n) (SHIFT' n₁) (congS SHIFT' x) (congS SHIFT' y) i i₁
  bbb : ∀{Γ τ₁ τ₂} (n : NeutralTerm Γ (τ₁ × τ₂)) → SHIFT' n ≡ pair (SHIFT' (proj₁ n)) (SHIFT' (proj₂ n))
  bbb var = refl
  bbb (proj₁ n) = ETA _
  bbb (proj₂ n) = ETA _
  _ : ∀{Γ τ₁ τ₂} (n : NeutralTerm Γ (τ₁ × τ₂)) → PROJ₁ (SHIFT' n) ≡ SHIFT' (proj₁ n)
  _ = λ _ → refl
  LR : ∀ τ Γ → NeutralTerm Γ τ → Type (ℓ-max ℓq ℓq')
  LR (↑ x) Γ n = SHIFT' n ≡ shift n
  LR (τ₁ × τ₂) Γ n = Σ (LR τ₁ Γ (proj₁ n)) λ _ → LR τ₂ Γ (proj₂ n)
  LR ⊤ Γ n = SHIFT' n ≡ uniq
  open import Cubical.Data.Unit
  LR' : ∀ τ Γ → Contains' Γ τ → NeutralTerm Γ τ → Type (ℓ-max ℓq ℓq')
  LR' (↑ x) Γ ast n = SHIFT' n ≡ shift n
  LR' (τ₁ × τ₂) Γ root n = Σ (LR' τ₁ Γ (left root) (proj₁ var)) λ _ → LR' τ₂ Γ (right root) (proj₂ var)
  LR' (τ₁ × τ₂) Γ (left ast) n = {!!}
  LR' (τ₁ × τ₂) Γ (right ast) n = {!!}
  LR' ⊤ Γ ast n = SHIFT' n ≡ uniq
  --BRRR' : ∀{τ Γ} (n : NeutralTerm Γ τ) → LR τ Γ n
  --test' : ∀{Γ x}{n : NeutralTerm Γ (↑ x)} → SHIFT' n ≡ shift n
  --test'' : ∀{Γ}{n : NeutralTerm Γ ⊤} → SHIFT' n ≡ uniq
  --BRRR' {τ = ↑ x} n = test'
  --BRRR' {τ = τ × τ₁} n = {!BRRR' (proj₁ n)!} , {!!}
  --BRRR' {τ = ⊤} n = test'' {n = n}
  --test' {n = var} = refl
  --test' {n = proj₁ n} = BRRR' n .fst
  --test' {n = proj₂ n} = BRRR' n .snd
  --test' {n = symb f x} = refl
  --test'' {n = var} = refl
  --test'' {n = proj₁ n} = BRRR' n .fst
  --test'' {n = proj₂ n} = BRRR' n .snd
  ----SOMANY : ∀{Δ Γ τ} (n : NeutralTerm Γ τ) (m : NeutralTerm Δ Γ) → SHIFT' (Ne/Ne n m) ≡ Nf/Nf (SHIFT' n) (SHIFT' m)
  ----SOMANY n m = {!!}
  MUST : ∀ τ Γ ast → LR τ Γ (UNIVNe ast)
  MUST (↑ x) _ root = refl
  MUST (τ₁ × τ₂) _ root =  MUST τ₁ (τ₁ × τ₂) (left root) , MUST _ _ (right root) --MUST τ₁ Γ (left root)  , MUST τ₂ Γ (right root)
  MUST ⊤ _ root = refl
  MUST (↑ x) Γ (left ast) = {!MUST (↑ x) Γ!}
  MUST (τ₁ × τ₂) Γ (left ast) = {!!}
  MUST ⊤ Γ (left ast) = {!!}
  MUST τ _ (right ast) = {!!} --MUST _ _ ast .snd

  KIST : ∀ τ Γ ast → LR τ Γ (UNIVNe ast)
  KIST (↑ x) Γ root = refl
  KIST (τ₁ × τ₂) Γ root = {!!} , {!!}
  KIST ⊤ Γ root = refl
  KIST _ Γ (left ast) = KIST _ _ ast .fst
  KIST _ Γ (right ast) = KIST _ _ ast .snd

  NIST : ∀ τ → LR τ τ var
  NIST (↑ x) = refl
  NIST (τ₁ × τ₂) = {!!} , {!!} --KIST τ₁ _ (left root) , KIST τ₂ _ (right root)
  NIST ⊤ = refl

  BRRR : ∀{τ Γ} (n : NeutralTerm Γ τ) → LR τ Γ n
  BRRR var = {!!} --MUST _ _ root
  BRRR (proj₁ n) = BRRR n .fst
  BRRR (proj₂ n) = BRRR n .snd
  BRRR (symb f x) = refl
  --BRRR {τ = ↑ x} {n = var} = refl
  --BRRR {τ = ↑ x} {n = proj₁ n} = BRRR {n = n} .fst
  --BRRR {τ = ↑ x} {n = proj₂ n} = BRRR {n = n} .snd
  --BRRR {τ = ↑ x} {n = symb f x₁} = refl
  --BRRR {τ = τ × τ₁} {n = n} = BRRR {n = proj₁ n} , BRRR {n = proj₂ n}
  --BRRR {τ = ⊤} = {!!}
  --ccc : ∀{Γ τ₁ τ₂} (n : NeutralTerm Γ (τ₁ × τ₂)) → SHIFT' n ≡ pair () ()
  --bbb (isSetNe n n₁ x y i i₁) = {!!}
  --COMM₁ : ∀{Γ τ₁ τ₂} (n : NeutralTerm Γ (τ₁ × τ₂)) → PROJ₁ (SHIFT' n) ≡ SHIFT' (proj₁ n)
  --COMM₁ n = refl
  test' : ∀{Γ x}{n : NeutralTerm Γ (↑ x)} → SHIFT' n ≡ shift n
  test' {n = var} = refl
  test' {n = proj₁ n} = {!BRRR n .fst!}
  test' {n = proj₂ n} = {!BRRR n .snd!}
  test' {n = symb f x} = refl
  test : ∀{Γ x}{n : NeutralTerm Γ (↑ x)} → SHIFT' n ≡ shift n
  test {n = n} = BRRR n 
  --test {n = isSetNe n n₁ x y i i₁} = {!!}
  --SHIFT : ∀{Γ τ} → NeutralTerm Γ τ → NormalForm Γ τ
  --SHIFT {τ = ↑ x} n = shift n
  --SHIFT {τ = τ₁ × τ₂} var = ID
  --SHIFT {τ = τ₁ × τ₂} (proj₁ n) = Nf/Ne PI₁ n
  --SHIFT {τ = τ₁ × τ₂} (proj₂ n) = Nf/Ne PI₂ n
  --SHIFT {τ = τ₁ × τ₂} (isSetNe n n₁ x y i i₁) = isSetNf (SHIFT n) (SHIFT n₁) (congS SHIFT x) (congS SHIFT y) i i₁
  --SHIFT {τ = ⊤} n = uniq
  --SHIFT n = Ne/Nf n ID
  --IDLNe' : ∀{Γ τ} (n : NeutralTerm Γ (↑ τ)) → (Ne/Nf n ID) ≡ shift n
  IDLNe : ∀{Γ τ} (n : NeutralTerm Γ τ) → (Ne/Nf n ID) ≡ SHIFT' n
  IDL : ∀{Γ τ} (n : NormalForm Γ τ) → Nf/Nf n ID ≡ n
  --IDLNe' var = refl
  --IDLNe' (proj₁ n) = {!congS PROJ₁!}
  --IDLNe' (proj₂ n) = {!!}
  --IDLNe' (symb f x) = {!!}
  --test' : ∀{Γ τ} (n : NeutralTerm Γ τ) → Ne/Nf n ID ≡ SHIFT' n
  --test' var = refl
  --test' (proj₁ n) = congS PROJ₁ (test' n)
  --test' (proj₂ n) = congS PROJ₂ (test' n)
  --test' (symb f x) = congS (λ z → shift (symb f z)) (IDL x)
  IDLNe var = refl
  IDLNe (proj₁ n) = congS PROJ₁ (IDLNe n) --∙ {!refl!}
  IDLNe (proj₂ n) = congS PROJ₂ (IDLNe n)
  IDLNe (symb f x) = congS (λ z → shift (symb f z)) (IDL x)
  --IDLNe (isSetNe n n₁ x y i i₁) = {!!}
  --uhoh {n = var} = refl
  --uhoh {n = proj₁ n} = {!uhoh {n = n}!}
  --uhoh {n = proj₂ n} = {!!}
  --uhoh {n = symb f x} = congS (λ z → shift (symb f z)) (IDL x)
  --uhoh {n = isSetNe n n₁ x y i i₁} = {!!}
  IDL (shift n) = IDLNe n ∙ test --IDLNe n --IDLNe n
  IDL (pair n₁ n₂) = cong₂ pair (IDL n₁) (IDL n₂)
  IDL uniq = refl
  --IDL (isSetNf n n₁ x y i i₁) = {!!}
  --ROJ₁' : ∀{τ₁ τ₂} → NeutralTerm (τ₁ × τ₂) τ₁
  --ROJ₂' : ∀{τ₁ τ₂} → NeutralTerm (τ₁ × τ₂) τ₂
  --NF : ∀ {τ} Γ → NormalForm Γ τ
  --NF {↑ x} Γ = shift {!!}
  --NF {τ × τ₁} = {!!}
  --NF {⊤} = {!!}
  --fum : (τ : Q.Ob) → NormalForm τ τ
  --fum (↑ _) = shift var
  --fum (τ₁ × τ₂) = pair {!fum τ₁!} {!!}
  --fum ⊤ = uniq
  --ID : ∀{τ} → NormalForm τ τ
  ----test : ∀{τ₁ τ₂ τ₃} → NormalForm ((τ₁ × τ₂) × τ₃) τ₁
  --ROJ₁ : ∀{τ₁ τ₂} → NormalForm (τ₁ × τ₂) τ₁
  --ROJ₂ : ∀{τ₁ τ₂} → NormalForm (τ₁ × τ₂) τ₂
  ----test {↑ x} = shift (proj₁ (proj₁ var))
  ----test {τ₁ × τ₂} = pair (com'''' (com'''' ROJ₁ ROJ₁) ROJ₁) (com'''' (com'''' ROJ₂ ROJ₁) ROJ₁)
  ----test {⊤} = uniq
  --ROJ₁ {↑ x} = shift (proj₁ var)
  --ROJ₁ {τ₁ × τ₂} = pair (Nf/Nf {!!} (PROJ₁ {!!})) {!!} --(com'''' ROJ₁ ROJ₁) (com'''' ROJ₂ (ROJ₁ {})
  --ROJ₁ {⊤} = uniq
  --ROJ₂ {τ₂ = ↑ x} = shift (proj₂ var)
  --ROJ₂ {τ₂ = τ₁ × τ₂} = pair {!!} {!!}
  --ROJ₂ {τ₂ = ⊤} = uniq
  --ID {↑ _} = shift var
  --ID {τ₁ × τ₂} = pair ROJ₁ ROJ₂
  --ID {⊤} = uniq
  |Nf| : Category {!!} {!!}
  |Nf| .ob = Q.Ob
  |Nf| .Hom[_,_] = NormalForm
  |Nf| .id = ID
  |Nf| ._⋆_ n m = Nf/Nf m n
  |Nf| .⋆IdL n = {!n!}
  |Nf| .⋆IdR = {!!}
  |Nf| .⋆Assoc = {!!}
  |Nf| .isSetHom = {!!} --isSetNf
  --Nf : CartesianCategory {!!} {!!}
  --Nf .fst = |Nf|
  --Nf .snd .fst = {!!}
  --Nf .snd .snd = {!!}
