module Cubical.Categories.Constructions.Free.CartesianCategory.Nf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

private
  variable
    ℓq ℓq' : Level

module _ (Q : ×Quiver ℓq ℓq')
  where
  open Category
  private
    module Q = ×QuiverNotation Q

  data NormalForm : (Γ τ : Q.Ob) → Type (ℓ-max ℓq ℓq')
  --data NormalForm' : (Γ τ : Q.Ob) → Type (ℓ-max ℓq ℓq')
  data NeutralTerm : (Γ τ : Q.Ob) → Type (ℓ-max ℓq ℓq')

  data NeutralTerm where
    var : ∀{τ} → NeutralTerm τ τ
    proj₁ : ∀{Γ τ₁ τ₂} → NeutralTerm Γ (τ₁ × τ₂) → NeutralTerm Γ τ₁
    proj₂ : ∀{Γ τ₁ τ₂} → NeutralTerm Γ (τ₁ × τ₂) → NeutralTerm Γ τ₂
    symb : ∀{Γ} (f : Q.mor) → NormalForm Γ (Q.dom f) → NeutralTerm Γ (↑ (Q.cod f))
    -- NOTE: we don't actually need that NeutralTerm is a hSet, so no need to throw those extra paths in
    -- SIKE: actually we do
    isSetNe : ∀{Γ τ} → isSet (NeutralTerm Γ τ)

  --data NormalForm' where
  --  -- shift only at ground types to enforce η-long normal forms
  --  shift : ∀{Γ τ} → NeutralTerm Γ (↑ τ) → NormalForm' Γ (↑ τ)
  --  pair : ∀{Γ τ₁ τ₂} → NormalForm' Γ τ₁ → NormalForm' Γ τ₂ → NormalForm' Γ (τ₁ × τ₂)
  --  uniq : ∀{Γ} → NormalForm' Γ ⊤

  data NormalForm where
    -- shift only at ground types to enforce η-long normal forms
    shift : ∀{Γ τ} → NeutralTerm Γ (↑ τ) → NormalForm Γ (↑ τ)
    pair : ∀{Γ τ₁ τ₂} → NormalForm Γ τ₁ → NormalForm Γ τ₂ → NormalForm Γ (τ₁ × τ₂)
    uniq : ∀{Γ} → NormalForm Γ ⊤
    -- either directly stipulate this, or show that NormalForm is a hSet another way
    isSetNf : ∀{Γ τ} → isSet (NormalForm Γ τ)

  ---- this should be true, but requires some work (see HoTT book)
  --Hed-Lem' : ∀{Γ τ} (ne₁ ne₂ : NeutralTerm Γ τ) → shift ne₁ ≡ shift ne₂ → ne₁ ≡ ne₂
  --Hed-Lem' ne₁ ne₂ p = {!!}

  --Hed-Lem : ∀{Γ τ} (ne₁ ne₂ : NeutralTerm Γ τ) → Dec (ne₁ ≡ ne₂) → Dec (shift ne₁ ≡ shift ne₂)
  --Hed-Lem ne₁ ne₂ (yes p) = yes (congS shift p)
  --Hed-Lem ne₁ ne₂ (no ¬p) = no (λ q → ¬p {!q!})

  --Hed-Ne : ∀{Γ τ} → Discrete (NeutralTerm Γ τ)
  --Hed : ∀{Γ τ} → Discrete (NormalForm' Γ τ)

  --Hed-Ne ne₁ ne₂ = {!!}

  --Hed {τ = ↑ x} (shift ne₁) (shift ne₂) = {!Hed-Ne ne₁ ne₂!}
  --Hed {τ = τ₁ × τ₂} n₁ n₂ = {!!}
  --Hed {τ = ⊤} uniq uniq = yes refl

  -- this is the "type directed" shift
  SHIFT : ∀{Γ τ} → NeutralTerm Γ τ → NormalForm Γ τ
  SHIFT {τ = ↑ _} = shift
  SHIFT {τ = τ₁ × τ₂} n = pair (SHIFT $ proj₁ n) (SHIFT $ proj₂ n)
  SHIFT {τ = ⊤} _ = uniq
  -- there's also a constructor-directed (syntax directed?) shift, but it doesn't obviously have any nice properties?

  ID : ∀{τ} → NormalForm τ τ
  ID = SHIFT var

  -- TODO: do we *really* need to use this?
  -- I don't feel like I super understand why we need this, but it just seems like we do
  PROJ₁ : ∀{Γ τ₁ τ₂} → NormalForm Γ (τ₁ × τ₂) → NormalForm Γ τ₁
  PROJ₁ (pair n₁ _) = n₁
  PROJ₁ (isSetNf n m p q i j) = isSetNf (PROJ₁ n) (PROJ₁ m) (congS PROJ₁ p) (congS PROJ₁ q) i j

  PROJ₂ : ∀{Γ τ₁ τ₂} → NormalForm Γ (τ₁ × τ₂) → NormalForm Γ τ₂
  PROJ₂ (pair _ n₂) = n₂
  PROJ₂ (isSetNf n m p q i j) = isSetNf (PROJ₂ n) (PROJ₂ m) (congS PROJ₂ p) (congS PROJ₂ q) i j

  -- substitution, in composition order (*not* "diagramatic" order)
  Nf/Nf : ∀{Γ Δ τ} → NormalForm Δ τ → NormalForm Γ Δ → NormalForm Γ τ
  Ne/Nf : ∀{Γ Δ τ} → NeutralTerm Δ τ → NormalForm Γ Δ → NormalForm Γ τ
  Nf/Ne : ∀{Γ Δ τ} → NormalForm Δ τ → NeutralTerm Γ Δ → NormalForm Γ τ
  Ne/Ne : ∀{Γ Δ τ} → NeutralTerm Δ τ → NeutralTerm Γ Δ → NeutralTerm Γ τ

  Nf/Nf (shift ne) nf = Ne/Nf ne nf
  Nf/Nf (pair nf₁ nf₂) nf₃ = pair (Nf/Nf nf₁ nf₃) (Nf/Nf nf₂ nf₃)
  Nf/Nf uniq _ = uniq
  Nf/Nf (isSetNf n m p q i j) nf₂ = isSetNf (Nf/Nf n nf₂) (Nf/Nf m nf₂) (cong₂ Nf/Nf p refl) (cong₂ Nf/Nf q refl) i j

  Ne/Nf var = idfun _
  Ne/Nf (proj₁ ne) nf = PROJ₁ $ Ne/Nf ne nf
  Ne/Nf (proj₂ ne) nf = PROJ₂ $ Ne/Nf ne nf
  Ne/Nf (symb f nf₁) nf₂ = shift $ symb f $ Nf/Nf nf₁ nf₂
  Ne/Nf (isSetNe n m p q i j) nf = isSetNf _ _
    (congS (λ x → Ne/Nf x nf) p)
    (congS (λ x → Ne/Nf x nf) q)
    i j

  Nf/Ne (shift ne₁) ne₂ = shift $ Ne/Ne ne₁ ne₂
  Nf/Ne (pair nf₁ nf₂) ne = pair (Nf/Ne nf₁ ne) (Nf/Ne nf₂ ne)
  Nf/Ne uniq _ = uniq
  Nf/Ne (isSetNf n m p q i j) ne = isSetNf (Nf/Ne n ne) (Nf/Ne m ne) (cong₂ Nf/Ne p refl) (cong₂ Nf/Ne q refl) i j

  Ne/Ne var = idfun _
  Ne/Ne (proj₁ ne₁) ne₂ = proj₁ $ Ne/Ne ne₁ ne₂
  Ne/Ne (proj₂ ne₁) ne₂ = proj₂ $ Ne/Ne ne₁ ne₂
  Ne/Ne (symb f nf) ne = symb f $ Nf/Ne nf ne
  Ne/Ne (isSetNe ne₁ ne₂ p q i j) ne₃ = isSetNe _ _ (congS (λ x → Ne/Ne x ne₃) p) (congS (λ x → Ne/Ne x ne₃) q) i j

  SHIFT-isSetNe : ∀ {Γ τ} →
    (n₁ n₂ : NeutralTerm Γ τ)
    (p q : n₁ ≡ n₂) →
    congS (congS SHIFT) (isSetNe n₁ n₂ p q) ≡ isSetNf (SHIFT n₁) (SHIFT n₂) (congS SHIFT p) (congS SHIFT q)
  SHIFT-isSetNe _ _ _ _ = isSet→isGroupoid isSetNf _ _ _ _ _ _

  IDL : ∀{Γ τ} (n : NormalForm Γ τ) → Nf/Nf n ID ≡ n
  IDL-Ne : ∀{Γ τ} (n : NeutralTerm Γ τ) → Ne/Nf n ID ≡ SHIFT n

  IDL (shift ne) = IDL-Ne ne
  IDL (pair nf₁ nf₂) = cong₂ pair (IDL nf₁) (IDL nf₂)
  IDL uniq = refl
  IDL (isSetNf n₁ n₂ p q i j) k = isSetNf (IDL n₁ k) (IDL n₂ k) (congS (λ x → IDL x k) p) (congS (λ x → IDL x k) q) i j

  IDL-Ne var = refl
  IDL-Ne (proj₁ ne) = congS PROJ₁ $ IDL-Ne ne
  IDL-Ne (proj₂ ne) = congS PROJ₂ $ IDL-Ne ne
  IDL-Ne (symb f nf) = congS (shift ∘S symb f) $ IDL nf
  IDL-Ne (isSetNe n m p q i j) = {!!}

  _∘proj₁ : ∀{Γ Δ τ} → NeutralTerm Γ τ → NeutralTerm (Γ × Δ) τ
  _∘PROJ₁ : ∀{Γ Δ τ} → NormalForm Γ τ → NormalForm (Γ × Δ) τ

  var ∘proj₁ = proj₁ var
  (proj₁ ne) ∘proj₁ = proj₁ $ ne ∘proj₁
  (proj₂ ne) ∘proj₁ = proj₂ $ ne ∘proj₁
  (symb f nf) ∘proj₁ = symb f $ nf ∘PROJ₁

  (shift ne) ∘PROJ₁ = shift $ ne ∘proj₁
  (pair nf₁ nf₂) ∘PROJ₁ = pair (nf₁ ∘PROJ₁) (nf₂ ∘PROJ₁)
  uniq ∘PROJ₁ = uniq
  (isSetNf n₁ n₂ p q i j) ∘PROJ₁ = isSetNf (n₁ ∘PROJ₁) (n₂ ∘PROJ₁) (congS _∘PROJ₁ p) (congS _∘PROJ₁ q) i j

  _∘proj₂ : ∀{Γ Δ τ} → NeutralTerm Δ τ → NeutralTerm (Γ × Δ) τ
  _∘PROJ₂ : ∀{Γ Δ τ} → NormalForm Δ τ → NormalForm (Γ × Δ) τ

  var ∘proj₂ = proj₂ var
  (proj₁ ne) ∘proj₂ = proj₁ $ ne ∘proj₂
  (proj₂ ne) ∘proj₂ = proj₂ $ ne ∘proj₂
  (symb f nf) ∘proj₂ = symb f $ nf ∘PROJ₂

  (shift ne) ∘PROJ₂ = shift $ ne ∘proj₂
  (pair nf₁ nf₂) ∘PROJ₂ = pair (nf₁ ∘PROJ₂) (nf₂ ∘PROJ₂)
  uniq ∘PROJ₂ = uniq
  (isSetNf n₁ n₂ p q i j) ∘PROJ₂ = isSetNf (n₁ ∘PROJ₂) (n₂ ∘PROJ₂) (congS _∘PROJ₂ p) (congS _∘PROJ₂ q) i j

  -- these types of proofs should somehow be automatic...
  SHIFT-∘proj₁ : ∀{Γ Δ τ} {ne : NeutralTerm Γ τ} → SHIFT {Γ = Γ × Δ} (ne ∘proj₁) ≡ (SHIFT ne) ∘PROJ₁
  SHIFT-∘proj₁ {τ = ↑ x} = refl
  SHIFT-∘proj₁ {τ = τ₁ × τ₂} = cong₂ pair SHIFT-∘proj₁ SHIFT-∘proj₁
  SHIFT-∘proj₁ {τ = ⊤} = refl

  SHIFT-∘proj₂ : ∀{Γ Δ τ} {ne : NeutralTerm Δ τ} → SHIFT {Γ = Γ × Δ} (ne ∘proj₂) ≡ (SHIFT ne) ∘PROJ₂
  SHIFT-∘proj₂ {τ = ↑ x} = refl
  SHIFT-∘proj₂ {τ = τ₁ × τ₂} = cong₂ pair SHIFT-∘proj₂ SHIFT-∘proj₂
  SHIFT-∘proj₂ {τ = ⊤} = refl

  -- ast of pairs with "pointed" NormalForm
  data Embedded Γ τ (n : NormalForm Γ τ) : Q.Ob → Type (ℓ-max ℓq ℓq') where
    root : Embedded Γ τ n τ
    left : ∀{τ' τ''} → Embedded Γ τ n τ' → NormalForm Γ τ'' → Embedded Γ τ n (τ' × τ'')
    right : ∀{τ' τ''} → NormalForm Γ τ' → Embedded Γ τ n τ'' → Embedded Γ τ n (τ' × τ'')

  --FOO : ∀{Γ τ Δ} → (n₁ n₂ : NormalForm Γ τ) (p q : n₁ ≡ n₂) →
  --  congS (λ x → Embedded Γ τ x Δ) p ≡ congS (λ x → Embedded Γ τ x Δ) q
  --FOO {Γ} {τ} {Δ} n₁ n₂ p q = congS (congS (λ x → Embedded Γ τ x Δ))
  --  (isSetNf _ _ p q)
  ----Embedded Γ τ (isSetNf n₁ n₂ p q i j) Δ

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
  β₁-Nf/Nf uniq _ _ = refl
  β₁-Nf/Nf (isSetNf nf₁ nf₂ p q i j) nf₃ nf₄ k = isSetNf _ _
    (congS (λ x → β₁-Nf/Nf x nf₃ nf₄ k) p)
    (congS (λ x → β₁-Nf/Nf x nf₃ nf₄ k) q)
    i j

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
  β₂-Nf/Nf (isSetNf nf₁ nf₂ p q i j) nf₃ nf₄ k = isSetNf _ _
    (congS (λ x → β₂-Nf/Nf x nf₃ nf₄ k) p)
    (congS (λ x → β₂-Nf/Nf x nf₃ nf₄ k) q)
    i j

  --IDR-lem-Ne/Nf : ∀{Γ τ Δ} →
  --  (n : NormalForm Γ τ)
  --  (ast : Embedded Γ τ n Δ) →
  --  Ne/Nf ⟨ ast ⟩ ∣ ast ∣ ≡ n
  --IDR-lem-Ne/Nf {τ = ↑ x} n root = refl
  --IDR-lem-Ne/Nf {τ = ↑ x} n (left ast x₁) = {!!}
  --IDR-lem-Ne/Nf {τ = ↑ x} n (right x₁ ast) = {!!}
  --IDR-lem-Ne/Nf {τ = τ₁ × τ₂} n root = refl
  --IDR-lem-Ne/Nf {τ = τ₁ × τ₂} n (left ast x) = {!!}
  --IDR-lem-Ne/Nf {τ = τ₁ × τ₂} n (right x ast) = {!!}
  --IDR-lem-Ne/Nf {τ = ⊤} n root = refl
  --IDR-lem-Ne/Nf {τ = ⊤} uniq (left ast x) = {!!} ∙ IDR-lem-Ne/Nf uniq ast
  --IDR-lem-Ne/Nf {τ = ⊤} uniq (right x ast) = {!!} ∙ IDR-lem-Ne/Nf uniq ast
  ----IDR-lem-Ne/Nf {τ = ⊤} (isSetNf n₁ n₂ p q i j) root k = isSetNf _ _
  ----  (congS (λ x → IDR-lem-Ne/Nf x root k) p)
  ----  (congS (λ x → IDR-lem-Ne/Nf x root k) q)
  ----  i j
  --IDR-lem-Ne/Nf {τ = ⊤} (isSetNf n₁ n₂ p q i j) (left ast x) = {!IDR-lem-Ne/Nf (isSetNf n₁ n₂ p q i j) ast!}
  --IDR-lem-Ne/Nf {τ = ⊤} (isSetNf n₁ n₂ p q i j) (right x ast) = {!!}

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
  IDR-lem {τ = τ₁ × τ₂} (isSetNf n₁ n₂ p q i j) ast = {!!}
  IDR-lem {τ = ⊤} uniq _ = refl
  IDR-lem {τ = ⊤} (isSetNf n₁ n₂ p q i j) ast = {!!}

  IDR : ∀{Γ τ} (n : NormalForm Γ τ) → Nf/Nf ID n ≡ n
  --IDR n = IDR-lem n root
  IDR (shift _) = refl
  IDR (pair n n₁) = {!!}
  IDR uniq = {!!}
  IDR (isSetNf n₁ n₂ p q i j) = {!!}

  Nf/Nf-PROJ₁ : ∀{Γ Δ τ₁ τ₂} (n₁ : NormalForm Δ (τ₁ × τ₂)) (n₂ : NormalForm Γ Δ) →
    Nf/Nf (PROJ₁ n₁) n₂ ≡ PROJ₁ (Nf/Nf n₁ n₂)
  Nf/Nf-PROJ₁ (pair _ _) _ = refl
  Nf/Nf-PROJ₁ (isSetNf n₁ n₂ p q i j) n₃ k = isSetNf _ _
    (congS (λ x → Nf/Nf-PROJ₁ x n₃ k) p)
    (congS (λ x → Nf/Nf-PROJ₁ x n₃ k) q)
    i j

  Nf/Nf-PROJ₂ : ∀{Γ Δ τ₁ τ₂} (n₁ : NormalForm Δ (τ₁ × τ₂)) (n₂ : NormalForm Γ Δ) →
    Nf/Nf (PROJ₂ n₁) n₂ ≡ PROJ₂ (Nf/Nf n₁ n₂)
  Nf/Nf-PROJ₂ (pair _ _) _ = refl
  Nf/Nf-PROJ₂ (isSetNf n₁ n₂ p q i j) n₃ k = isSetNf _ _
    (congS (λ x → Nf/Nf-PROJ₂ x n₃ k) p)
    (congS (λ x → Nf/Nf-PROJ₂ x n₃ k) q)
    i j

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
  ASSOC-Nf/Nf/Nf (isSetNf n₃ n₄ p q i j) n₂ n₁ k = isSetNf _ _
    (congS (λ x → ASSOC-Nf/Nf/Nf x n₂ n₁ k) p)
    (congS (λ x → ASSOC-Nf/Nf/Nf x n₂ n₁ k) q)
    i j

  ASSOC-Ne/Nf/Nf var _ _ = refl
  ASSOC-Ne/Nf/Nf (proj₁ n₃) n₂ n₁ = congS PROJ₁ (ASSOC-Ne/Nf/Nf n₃ n₂ n₁) ∙ sym (Nf/Nf-PROJ₁ (Ne/Nf n₃ n₂) n₁)
  ASSOC-Ne/Nf/Nf (proj₂ n₃) n₂ n₁ = congS PROJ₂ (ASSOC-Ne/Nf/Nf n₃ n₂ n₁) ∙ sym (Nf/Nf-PROJ₂ (Ne/Nf n₃ n₂) n₁)
  ASSOC-Ne/Nf/Nf (symb f nf) n₂ n₁ = congS (shift ∘S symb f) (ASSOC-Nf/Nf/Nf nf n₂ n₁)

  |Nf| : Category _ _
  |Nf| .ob = Q.Ob
  |Nf| .Hom[_,_] = NormalForm
  |Nf| .id = ID
  |Nf| ._⋆_ n m = Nf/Nf m n
  |Nf| .⋆IdL = IDL
  |Nf| .⋆IdR = IDR
  |Nf| .⋆Assoc n₁ n₂ n₃ = ASSOC-Nf/Nf/Nf n₃ n₂ n₁
  |Nf| .isSetHom = isSetNf

  --Nf : CartesianCategory {!!} {!!}
  --Nf .fst = |Nf|
  --Nf .snd .fst = {!!}
  --Nf .snd .snd = {!!}
