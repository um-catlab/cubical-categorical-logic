{-# OPTIONS --cubical --type-in-type #-}

module HyperDoc.Operational.Effects.Reduction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.ExtensionSystem
open import Cubical.Data.FinData renaming (rec to finRec)
open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.List.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (Discrete; ¬_)
import Cubical.Data.DescendingList.Strict.Properties
import Cubical.HITs.ListedFiniteSet as LF

------------------------------------------------------------------------
-- Section 1: inputs

record Signature : Type where
  field
    Op    : Type
    arity : Op → ℕ

open Signature

data Term (Σ : Signature) (X : Type) : Type where
  var : X → Term Σ X
  op  : (o : Op Σ) → (Fin (arity Σ o) → Term Σ X) → Term Σ X

record Polynomial : Type where
  constructor _◂_
  field
    Shape : Type
    size  : Shape → ℕ

open Polynomial

⟦_⟧ : Polynomial → Type → Type
⟦ P ⟧ X = Σ[ s ∈ Shape P ] (Fin (size P s) → X)

mapP : ∀ {P X Y} → (X → Y) → ⟦ P ⟧ X → ⟦ P ⟧ Y
mapP f (s , xs) = s , λ i → f (xs i)

-- A parametric, proposition-valued relation on the interpretation of p.
Relation : Polynomial → Type
Relation P =
  (X : hSet ℓ-zero) → (u v : ⟦ P ⟧ ⟨ X ⟩) → hProp ℓ-zero

SectionAt :
  (P : Polynomial) (Q : hSet ℓ-zero → hSet ℓ-zero) →
  hSet ℓ-zero → Type
SectionAt P Q X = ⟨ Q X ⟩ → ⟦ P ⟧ ⟨ X ⟩

IsSectionAt :
  (P : Polynomial) (Q : hSet ℓ-zero → hSet ℓ-zero)
  (X : hSet ℓ-zero) →
  (q : ⟦ P ⟧ ⟨ X ⟩ → ⟨ Q X ⟩) →
  SectionAt P Q X → Type
IsSectionAt P Q X q c = (u : ⟨ Q X ⟩) → q (c u) ≡ u

AlgebraAt :
  Signature → (hSet ℓ-zero → hSet ℓ-zero) → hSet ℓ-zero → Type
AlgebraAt Σ Q X =
  (o : Op Σ) →
  (Fin (arity Σ o) → ⟨ Q X ⟩) → ⟨ Q X ⟩

AlgebraStructure :
  Signature → (hSet ℓ-zero → hSet ℓ-zero) → Type
AlgebraStructure Σ Q = (X : hSet ℓ-zero) → AlgebraAt Σ Q X

------------------------------------------------------------------------
-- Section 2: construction

module Construction
  (Σ : Signature)
  (P : Polynomial)
  (R : Relation P)
  (Q : hSet ℓ-zero → hSet ℓ-zero)
  (q : (X : hSet ℓ-zero) → ⟦ P ⟧ ⟨ X ⟩ → ⟨ Q X ⟩)
  (q-resp : ∀ X u v → ⟨ R X u v ⟩ → q X u ≡ q X v)
  (M : ExtensionSystemFor (SET ℓ-zero) Q)
  (alg : AlgebraStructure Σ Q)
  where

  open ExtensionSystemFor M

  join : ∀ {X} → ⟨ Q (Q X) ⟩ → ⟨ Q X ⟩
  join = bind (Category.id (SET ℓ-zero))

  module At
    (X : hSet ℓ-zero)
    (term-isSet : isSet (Term Σ ⟨ X ⟩))
    (c : SectionAt P Q (Term Σ ⟨ X ⟩ , term-isSet))
    (q∘c : IsSectionAt P Q (Term Σ ⟨ X ⟩ , term-isSet)
      (q (Term Σ ⟨ X ⟩ , term-isSet)) c)
    where

    TermX : hSet ℓ-zero
    TermX = Term Σ ⟨ X ⟩ , term-isSet

    -- This is deliberately one layer of interpretation.  The operands
    -- of an operation are returned with η, as in reduction.pdf.
    interp : Term Σ ⟨ X ⟩ → ⟨ Q TermX ⟩
    interp (var x)     = η (var x)
    interp (op o args) = alg TermX o (λ i → η (args i))

    stepᵢ : ⟦ P ⟧ (Term Σ ⟨ X ⟩) → ⟦ P ⟧ (Term Σ ⟨ X ⟩)
    stepᵢ t = c (join (q _ (mapP interp t)))

    data _↦_ :
      ⟦ P ⟧ (Term Σ ⟨ X ⟩) →
      ⟦ P ⟧ (Term Σ ⟨ X ⟩) → Type where
      effect : ∀ {t} → t ↦ stepᵢ t

------------------------------------------------------------------------
-- Section 3.1: finite sets

ListP : Polynomial
ListP = ℕ ◂ λ n → n

data MonOp : Type where
  e ⊗ : MonOp

MonΣ : Signature
MonΣ .Op = MonOp
MonΣ .arity e = 0
MonΣ .arity ⊗ = 2

module FiniteSetModel where

  open LF renaming
    ( LFSet to Finite
    ; [] to ∅
    ; _∷_ to _∷ˢ_
    ; _++_ to _∪_
    ; trunc to Finite-isSet
    ; assoc-++ to ∪-assoc
    ; comm-++ to ∪-comm
    ; comm-++-[] to ∪-unit
    ; idem-++ to ∪-idem
    )

  toFinite : ∀ {X} → ⟦ ListP ⟧ X → Finite X
  toFinite (n , xs) = foldrFin _∷ˢ_ ∅ xs

  -- This is the kernel relation of the list-to-finite-set quotient.
  -- The constructors dup and comm of ListedFiniteSet ensure that it
  -- contains idempotence and commutativity.
  FiniteR : Relation ListP
  FiniteR X xs ys =
    (toFinite xs ≡ toFinite ys) ,
    Finite-isSet (toFinite xs) (toFinite ys)

  fromList : ∀ {X} → List X → ⟦ ListP ⟧ X
  fromList {X} = Iso.fun (lookup-tabulate-iso X)

  toFinite-fromList :
    ∀ {X} (xs : List X) →
    toFinite (fromList xs) ≡ foldr _∷ˢ_ ∅ xs
  toFinite-fromList [] = refl
  toFinite-fromList (x ∷ xs) =
    cong (x ∷ˢ_) (toFinite-fromList xs)

  FiniteR-idem :
    ∀ (X : hSet ℓ-zero) (x : ⟨ X ⟩) xs →
    ⟨ FiniteR X
      (fromList (x ∷ x ∷ xs))
      (fromList (x ∷ xs)) ⟩
  FiniteR-idem X x xs =
    toFinite-fromList (x ∷ x ∷ xs)
    ∙ LF.dup x (foldr _∷ˢ_ ∅ xs)
    ∙ sym (toFinite-fromList (x ∷ xs))

  FiniteR-comm :
    ∀ (X : hSet ℓ-zero) (x y : ⟨ X ⟩) xs →
    ⟨ FiniteR X
      (fromList (x ∷ y ∷ xs))
      (fromList (y ∷ x ∷ xs)) ⟩
  FiniteR-comm X x y xs =
    toFinite-fromList (x ∷ y ∷ xs)
    ∙ LF.comm x y (foldr _∷ˢ_ ∅ xs)
    ∙ sym (toFinite-fromList (y ∷ x ∷ xs))

  FiniteT : hSet ℓ-zero → hSet ℓ-zero
  FiniteT X = Finite ⟨ X ⟩ , Finite-isSet

  quotient : (X : hSet ℓ-zero) → ⟦ ListP ⟧ ⟨ X ⟩ → ⟨ FiniteT X ⟩
  quotient X = toFinite

  quotient-resp :
    ∀ X xs ys → ⟨ FiniteR X xs ys ⟩ →
    quotient X xs ≡ quotient X ys
  quotient-resp X xs ys r = r

  singleton : ∀ {X} → X → Finite X
  singleton x = x ∷ˢ ∅

  bindF : ∀ {X Y} → (X → Finite Y) → Finite X → Finite Y
  bindF {Y = Y} f =
    LF.Rec.f ∅
      (λ x ys → f x ∪ ys)
      (λ x y ys →
        f x ∪ (f y ∪ ys) ≡⟨ ∪-assoc (f x) (f y) ys ⟩
        (f x ∪ f y) ∪ ys ≡⟨ cong (_∪ ys) (∪-comm (f x) (f y)) ⟩
        (f y ∪ f x) ∪ ys ≡⟨ sym (∪-assoc (f y) (f x) ys) ⟩
        f y ∪ (f x ∪ ys) ∎)
      (λ x ys →
        f x ∪ (f x ∪ ys) ≡⟨ ∪-assoc (f x) (f x) ys ⟩
        (f x ∪ f x) ∪ ys ≡⟨ cong (_∪ ys) (∪-idem (f x)) ⟩
        f x ∪ ys ∎)
      Finite-isSet

  bindF-singleton :
    ∀ {X Y} (f : X → Finite Y) x → bindF f (singleton x) ≡ f x
  bindF-singleton f x = ∪-unit (f x)

  bindF-unit : ∀ {X} (xs : Finite X) → bindF singleton xs ≡ xs
  bindF-unit =
    LF.PropElim.f refl
      (λ x {xs} ih →
        singleton x ∪ bindF singleton xs
          ≡⟨ cong (singleton x ∪_) ih ⟩
        x ∷ˢ xs ∎)
      (λ xs → Finite-isSet _ _)

  bindF-assoc :
    ∀ {X Y Z} (f : X → Finite Y) (g : Y → Finite Z) xs →
    bindF g (bindF f xs) ≡ bindF (λ x → bindF g (f x)) xs
  bindF-assoc f g =
    LF.PropElim.f refl
      (λ x {xs} ih →
        bindF g (f x ∪ bindF f xs)
          ≡⟨ bindF-∪ g (f x) (bindF f xs) ⟩
        bindF g (f x) ∪ bindF g (bindF f xs)
          ≡⟨ cong (bindF g (f x) ∪_) ih ⟩
        bindF g (f x) ∪ bindF (λ y → bindF g (f y)) xs ∎)
      (λ xs → Finite-isSet _ _)
    where
    bindF-∪ :
      ∀ {A B} (h : A → Finite B) us vs →
      bindF h (us ∪ vs) ≡ bindF h us ∪ bindF h vs
    bindF-∪ h us vs =
      LF.PropElim.f refl
        (λ x {xs} ih → cong (h x ∪_) ih ∙ ∪-assoc (h x) _ _)
        (λ xs → Finite-isSet _ _)
        us

  finiteMonad : ExtensionSystemFor (SET ℓ-zero) FiniteT
  finiteMonad .ExtensionSystemFor.η = singleton
  finiteMonad .ExtensionSystemFor.bind = bindF
  finiteMonad .ExtensionSystemFor.bind-r = funExt bindF-unit
  finiteMonad .ExtensionSystemFor.bind-l =
    funExt λ x → bindF-singleton _ x
  finiteMonad .ExtensionSystemFor.bind-comp =
    funExt λ xs → bindF-assoc _ _ xs

  finiteAlg : AlgebraStructure MonΣ FiniteT
  finiteAlg X e args = ∅
  finiteAlg X ⊗ args = args zero ∪ args (suc zero)

  module Generic =
    Construction MonΣ ListP FiniteR FiniteT
      quotient quotient-resp finiteMonad finiteAlg

  module OrderedSection
    (A : hSet ℓ-zero)
    (_>_ : ⟨ A ⟩ → ⟨ A ⟩ → Type)
    (A-discrete : Discrete ⟨ A ⟩)
    (>-isProp : ∀ {x y} → isProp (x > y))
    (tri : ∀ x y →
      Cubical.Data.DescendingList.Strict.Properties.Tri
        ⟨ A ⟩ _>_ (y > x) (x ≡ y) (x > y))
    (>-trans : ∀ {x y z} → x > y → y > z → x > z)
    (>-irrefl : ∀ {x} → ¬ x > x)
    where

    import Cubical.Data.DescendingList.Strict ⟨ A ⟩ _>_ as Strict
    import Cubical.Data.DescendingList.Strict.Properties
      ⟨ A ⟩ _>_ as StrictProperties
    module Sort = StrictProperties.IsoToLFSet
      A-discrete >-isProp tri >-trans >-irrefl

    forget : Strict.SDL → List ⟨ A ⟩
    forget Strict.[] = []
    forget (Strict.cons x xs _) = x ∷ forget xs

    forget-unsort :
      (xs : Strict.SDL) →
      toFinite (Iso.fun (lookup-tabulate-iso ⟨ A ⟩) (forget xs))
        ≡ StrictProperties.unsort xs
    forget-unsort Strict.[] = refl
    forget-unsort (Strict.cons x xs x>xs) =
      cong (x LF.∷_) (forget-unsort xs)

    section : SectionAt ListP FiniteT A
    section xs =
      Iso.fun (lookup-tabulate-iso ⟨ A ⟩) (forget (Sort.sort xs))

    section-law :
      IsSectionAt ListP FiniteT A (quotient A) section
    section-law xs =
      forget-unsort (Sort.sort xs) ∙ Sort.unsort∘sort xs

  -- The only local assumptions are precisely those used to sort and
  -- deduplicate terms.  All quotient, monad, and algebra data above are
  -- concrete and uniform.
  module OrderedReduction
    (X : hSet ℓ-zero)
    (term-isSet : isSet (Term MonΣ ⟨ X ⟩))
    (_>_ : Term MonΣ ⟨ X ⟩ → Term MonΣ ⟨ X ⟩ → Type)
    (term-discrete : Discrete (Term MonΣ ⟨ X ⟩))
    (>-isProp : ∀ {x y} → isProp (x > y))
    (tri : ∀ x y →
      Cubical.Data.DescendingList.Strict.Properties.Tri
        (Term MonΣ ⟨ X ⟩) _>_ (y > x) (x ≡ y) (x > y))
    (>-trans : ∀ {x y z} → x > y → y > z → x > z)
    (>-irrefl : ∀ {x} → ¬ x > x)
    where

    TermX : hSet ℓ-zero
    TermX = Term MonΣ ⟨ X ⟩ , term-isSet

    module Canonical = OrderedSection
      TermX _>_ term-discrete >-isProp tri >-trans >-irrefl

    module Reduction = Generic.At
      X term-isSet Canonical.section Canonical.section-law

    step₁ : ⟦ ListP ⟧ (Term MonΣ ⟨ X ⟩) →
            ⟦ ListP ⟧ (Term MonΣ ⟨ X ⟩)
    step₁ = Reduction.stepᵢ

    _↦₁_ : ⟦ ListP ⟧ (Term MonΣ ⟨ X ⟩) →
            ⟦ ListP ⟧ (Term MonΣ ⟨ X ⟩) → Type
    _↦₁_ = Reduction._↦_
