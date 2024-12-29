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
    isSetNe : ∀{Γ τ} → isSet (NeutralTerm Γ τ)
  data NormalForm where
    shift : ∀{Γ τ} → NeutralTerm Γ (↑ τ) → NormalForm Γ (↑ τ)
    pair : ∀{Γ τ₁ τ₂} → NormalForm Γ τ₁ → NormalForm Γ τ₂ → NormalForm Γ (τ₁ × τ₂)
    uniq : ∀{Γ} → NormalForm Γ ⊤
    isSetNf : ∀{Γ τ} → isSet (NormalForm Γ τ)
  data Contains (τ : Q.Ob) : (Γ : Q.Ob) → Type ℓq where
    root : Contains τ τ
    left : ∀{Γ Δ} → Contains τ Γ → Contains τ (Γ × Δ)
    right : ∀{Γ Δ} → Contains τ Δ → Contains τ (Γ × Δ)
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
  PROJ₁ (isSetNf n m p q i j) = isSetNf (PROJ₁ n) (PROJ₁ m) (congS PROJ₁ p) (congS PROJ₁ q) i j
  PROJ₂ : ∀{Γ τ₁ τ₂} → NormalForm Γ (τ₁ × τ₂) → NormalForm Γ τ₂
  PROJ₂ (pair _ m) = m
  PROJ₂ (isSetNf n m p q i j) = isSetNf (PROJ₂ n) (PROJ₂ m) (congS PROJ₂ p) (congS PROJ₂ q) i j
  --ETA : ∀{Γ τ₁ τ₂} (n : NormalForm Γ (τ₁ × τ₂)) → pair (PROJ₁ n) (PROJ₂ n) ≡ n
  --ETA (pair n n₁) = refl
  Nf/Nf : ∀{Γ Δ τ} → NormalForm Δ τ → NormalForm Γ Δ → NormalForm Γ τ
  Ne/Nf : ∀{Γ Δ τ} → NeutralTerm Δ τ → NormalForm Γ Δ → NormalForm Γ τ
  Nf/Ne : ∀{Γ Δ τ} → NormalForm Δ τ → NeutralTerm Γ Δ → NormalForm Γ τ
  Ne/Ne : ∀{Γ Δ τ} → NeutralTerm Δ τ → NeutralTerm Γ Δ → NeutralTerm Γ τ
  Nf/Nf (shift x) x₁ = Ne/Nf x x₁
  Nf/Nf (pair x x₂) x₁ = pair (Nf/Nf x x₁) (Nf/Nf x₂ x₁)
  Nf/Nf uniq x₁ = uniq
  Nf/Nf (isSetNf x x₂ x₃ y i i₁) x₁ = isSetNf (Nf/Nf x x₁) (Nf/Nf x₂ x₁) (cong₂ Nf/Nf x₃ refl) (cong₂ Nf/Nf y refl) i i₁
  Ne/Nf var x₁ = x₁
  Ne/Nf (proj₁ x) x₁ = PROJ₁ (Ne/Nf x x₁)
  Ne/Nf (proj₂ x) x₁ = PROJ₂ (Ne/Nf x x₁)
  Ne/Nf (symb f x) x₁ = shift (symb f (Nf/Nf x x₁))
  Ne/Nf (isSetNe x x₂ x₃ y i i₁) x₁ = isSetNf (Ne/Nf x x₁) (Ne/Nf x₂ x₁) (cong₂ Ne/Nf x₃ refl) (cong₂ Ne/Nf y refl) i i₁
  Nf/Ne (shift x) x₁ = shift (Ne/Ne x x₁)
  Nf/Ne (pair x x₂) x₁ = pair (Nf/Ne x x₁) (Nf/Ne x₂ x₁)
  Nf/Ne uniq x₁ = uniq
  Nf/Ne (isSetNf x x₂ x₃ y i i₁) x₁ = isSetNf (Nf/Ne x x₁) (Nf/Ne x₂ x₁) (cong₂ Nf/Ne x₃ refl) (cong₂ Nf/Ne y refl) i i₁
  Ne/Ne var x₁ = x₁
  Ne/Ne (proj₁ x) x₁ = proj₁ (Ne/Ne x x₁)
  Ne/Ne (proj₂ x) x₁ = proj₂ (Ne/Ne x x₁)
  Ne/Ne (symb f x) x₁ = symb f (Nf/Ne x x₁)
  Ne/Ne (isSetNe x x₂ x₃ y i i₁) x₁ = isSetNe (Ne/Ne x x₁) (Ne/Ne x₂ x₁) (cong₂ Ne/Ne x₃ refl) (cong₂ Ne/Ne y refl) i i₁
  UNIV : ∀{Γ} (τ : Q.Ob) → Contains τ Γ → NormalForm Γ τ
  UNIV (↑ x) root = shift var
  UNIV (↑ x) (left AST) = Nf/Ne (UNIV _ AST) (proj₁ var)
  UNIV (↑ x) (right AST) = Nf/Ne (UNIV _ AST) (proj₂ var)
  UNIV (τ₁ × τ₂) root = pair (UNIV τ₁ (left root)) (UNIV τ₂ (right root))
  UNIV (τ₁ × τ₂) (left AST) = Nf/Ne (UNIV _ AST) (proj₁ var)
  UNIV (τ₁ × τ₂) (right AST) = Nf/Ne (UNIV _ AST) (proj₂ var)
  UNIV ⊤ AST = uniq
  ID : ∀{τ} → NormalForm τ τ
  ID = UNIV _ root
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
  |Nf| .isSetHom = isSetNf
  --Nf : CartesianCategory {!!} {!!}
  --Nf .fst = |Nf|
  --Nf .snd .fst = {!!}
  --Nf .snd .snd = {!!}
