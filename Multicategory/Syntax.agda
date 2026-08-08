{-

  The syntax: the free CARTESIAN CLOSED cartesian multicategory, with
  unit, products and functions.  There are no sums: every former here
  has a fibrewise universal property, and every closed term of a former
  is η-equal to an introduction, so no truncation is ever needed.

  Terms are an indexed HIT with substitution as a constructor, so the
  three clone laws are path constructors rather than substitution
  lemmas — there is no renaming/weakening grind, because weakening is
  just substitution by variables.  Contexts are arities: a term of
  Tm I Γ A has free variables indexed by I, typed by Γ.  Binding
  extends the arity by a point, I ⊎ Unit.

-}
module Multicategory.Syntax where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty

open import Multicategory.Cartesian

data Ty : Type where
  ⊤'   : Ty
  _×'_ : Ty → Ty → Ty
  _⇒'_ : Ty → Ty → Ty

infixr 5 _⇒'_
infixr 7 _×'_

Ctxt : Type → Type
Ctxt I = I → Ty

-- context extension: bind one more variable
_,,_ : {I : Type} → Ctxt I → Ty → Ctxt (I ⊎ Unit)
(Γ ,, A) (inl i) = Γ i
(Γ ,, A) (inr _) = A

infixl 5 _,,_

data Tm : (I : Type) (Γ : Ctxt I) (A : Ty) → Type₁ where
  var : {I : Type} {Γ : Ctxt I} (i : I) → Tm I Γ (Γ i)

  _⟪_⟫ : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J} {A : Ty}
    → Tm I Γ A → ((i : I) → Tm J Δ (Γ i)) → Tm J Δ A

  -- the clone laws
  ⟪⟫var : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J}
    (i : I) (f : (i : I) → Tm J Δ (Γ i))
    → (var i ⟪ f ⟫) ≡ f i
  ⟪⟫id : {I : Type} {Γ : Ctxt I} {A : Ty} (t : Tm I Γ A)
    → (t ⟪ var ⟫) ≡ t
  ⟪⟫⟪⟫ : {I J K : Type} {Γ : Ctxt I} {Δ : Ctxt J} {Θ : Ctxt K} {A : Ty}
    (t : Tm I Γ A)
    (f : (i : I) → Tm J Δ (Γ i)) (g : (j : J) → Tm K Θ (Δ j))
    → ((t ⟪ f ⟫) ⟪ g ⟫) ≡ (t ⟪ (λ i → f i ⟪ g ⟫) ⟫)

  -- unit
  tt' : {I : Type} {Γ : Ctxt I} → Tm I Γ ⊤'
  ⊤η : {I : Type} {Γ : Ctxt I} (t : Tm I Γ ⊤') → t ≡ tt'

  -- products
  pair : {I : Type} {Γ : Ctxt I} {A B : Ty}
    → Tm I Γ A → Tm I Γ B → Tm I Γ (A ×' B)
  fst' : {I : Type} {Γ : Ctxt I} {A B : Ty} → Tm I Γ (A ×' B) → Tm I Γ A
  snd' : {I : Type} {Γ : Ctxt I} {A B : Ty} → Tm I Γ (A ×' B) → Tm I Γ B

  pair-nat : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J} {A B : Ty}
    (a : Tm I Γ A) (b : Tm I Γ B) (f : (i : I) → Tm J Δ (Γ i))
    → (pair a b ⟪ f ⟫) ≡ pair (a ⟪ f ⟫) (b ⟪ f ⟫)
  fst-nat : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J} {A B : Ty}
    (t : Tm I Γ (A ×' B)) (f : (i : I) → Tm J Δ (Γ i))
    → (fst' t ⟪ f ⟫) ≡ fst' (t ⟪ f ⟫)
  snd-nat : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J} {A B : Ty}
    (t : Tm I Γ (A ×' B)) (f : (i : I) → Tm J Δ (Γ i))
    → (snd' t ⟪ f ⟫) ≡ snd' (t ⟪ f ⟫)

  ×β₁ : {I : Type} {Γ : Ctxt I} {A B : Ty}
    (a : Tm I Γ A) (b : Tm I Γ B) → fst' (pair a b) ≡ a
  ×β₂ : {I : Type} {Γ : Ctxt I} {A B : Ty}
    (a : Tm I Γ A) (b : Tm I Γ B) → snd' (pair a b) ≡ b
  ×η : {I : Type} {Γ : Ctxt I} {A B : Ty}
    (t : Tm I Γ (A ×' B)) → pair (fst' t) (snd' t) ≡ t

  -- functions
  lam : {I : Type} {Γ : Ctxt I} {A B : Ty}
    → Tm (I ⊎ Unit) (Γ ,, A) B → Tm I Γ (A ⇒' B)
  app : {I : Type} {Γ : Ctxt I} {A B : Ty}
    → Tm I Γ (A ⇒' B) → Tm I Γ A → Tm I Γ B

  -- NB: the extended environments are FORDED — passed as a variable
  -- with equations pinning it — rather than written as a Sum.elim.  A
  -- Sum.elim in the right-hand side is stuck on a variable index, which
  -- blocks both the boundary computation and the termination check of
  -- any eliminator.
  lam-nat : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J} {A B : Ty}
    (t : Tm (I ⊎ Unit) (Γ ,, A) B) (f : (i : I) → Tm J Δ (Γ i))
    (f↑ : (i : I ⊎ Unit) → Tm (J ⊎ Unit) (Δ ,, A) ((Γ ,, A) i))
    (f↑l : (i : I) → f↑ (inl i) ≡ (f i ⟪ (λ j → var (inl j)) ⟫))
    (f↑r : f↑ (inr tt) ≡ var (inr tt))
    → (lam t ⟪ f ⟫) ≡ lam (t ⟪ f↑ ⟫)
  app-nat : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J} {A B : Ty}
    (t : Tm I Γ (A ⇒' B)) (u : Tm I Γ A) (f : (i : I) → Tm J Δ (Γ i))
    → (app t u ⟪ f ⟫) ≡ app (t ⟪ f ⟫) (u ⟪ f ⟫)

  ⇒β : {I : Type} {Γ : Ctxt I} {A B : Ty}
    (t : Tm (I ⊎ Unit) (Γ ,, A) B) (u : Tm I Γ A)
    (f : (i : I ⊎ Unit) → Tm I Γ ((Γ ,, A) i))
    (fl : (i : I) → f (inl i) ≡ var i) (fr : f (inr tt) ≡ u)
    → app (lam t) u ≡ (t ⟪ f ⟫)
  ⇒η : {I : Type} {Γ : Ctxt I} {A B : Ty} (t : Tm I Γ (A ⇒' B))
    → lam (app (t ⟪ (λ j → var (inl j)) ⟫) (var (inr tt))) ≡ t

  trunc : {I : Type} {Γ : Ctxt I} {A : Ty} → isSet (Tm I Γ A)

infixl 8 _⟪_⟫

-- Eliminating into a prop-valued motive: every path constructor is
-- discharged at once, so a client only supplies the point cases.  The
-- logical predicates of Multicategory.Canonicity are prop-valued, so
-- this is the only eliminator they need.
module ElimProp {ℓ} {D : {I : Type} {Γ : Ctxt I} {A : Ty} → Tm I Γ A → Type ℓ}
  (isPropD : {I : Type} {Γ : Ctxt I} {A : Ty} (t : Tm I Γ A) → isProp (D t))
  (dvar : {I : Type} {Γ : Ctxt I} (i : I) → D (var {Γ = Γ} i))
  (d⟪⟫ : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J} {A : Ty}
    {t : Tm I Γ A} {f : (i : I) → Tm J Δ (Γ i)}
    → D t → ((i : I) → D (f i)) → D (t ⟪ f ⟫))
  (dtt : {I : Type} {Γ : Ctxt I} → D (tt' {I} {Γ}))
  (dpair : {I : Type} {Γ : Ctxt I} {A B : Ty}
    {a : Tm I Γ A} {b : Tm I Γ B} → D a → D b → D (pair a b))
  (dfst : {I : Type} {Γ : Ctxt I} {A B : Ty}
    {t : Tm I Γ (A ×' B)} → D t → D (fst' t))
  (dsnd : {I : Type} {Γ : Ctxt I} {A B : Ty}
    {t : Tm I Γ (A ×' B)} → D t → D (snd' t))
  (dlam : {I : Type} {Γ : Ctxt I} {A B : Ty}
    {t : Tm (I ⊎ Unit) (Γ ,, A) B} → D t → D (lam t))
  (dapp : {I : Type} {Γ : Ctxt I} {A B : Ty}
    {t : Tm I Γ (A ⇒' B)} {u : Tm I Γ A} → D t → D u → D (app t u))
  where

  elimProp : {I : Type} {Γ : Ctxt I} {A : Ty} (t : Tm I Γ A) → D t
  elimProp (var i) = dvar i
  elimProp (t ⟪ f ⟫) = d⟪⟫ (elimProp t) (λ i → elimProp (f i))
  elimProp tt' = dtt
  elimProp (pair a b) = dpair (elimProp a) (elimProp b)
  elimProp (fst' t) = dfst (elimProp t)
  elimProp (snd' t) = dsnd (elimProp t)
  elimProp (lam t) = dlam (elimProp t)
  elimProp (app t u) = dapp (elimProp t) (elimProp u)
  -- every path constructor: the motive is a prop, so the only work is
  -- writing down the two endpoints
  elimProp (⟪⟫var i f k) =
    isProp→PathP (λ k → isPropD (⟪⟫var i f k))
      (d⟪⟫ (dvar i) (λ i → elimProp (f i))) (elimProp (f i)) k
  elimProp (⟪⟫id t k) =
    isProp→PathP (λ k → isPropD (⟪⟫id t k))
      (d⟪⟫ (elimProp t) (λ i → dvar i)) (elimProp t) k
  elimProp (⟪⟫⟪⟫ t f g k) =
    isProp→PathP (λ k → isPropD (⟪⟫⟪⟫ t f g k))
      (d⟪⟫ (d⟪⟫ (elimProp t) (λ i → elimProp (f i)))
           (λ j → elimProp (g j)))
      (d⟪⟫ (elimProp t)
           (λ i → d⟪⟫ (elimProp (f i)) (λ j → elimProp (g j)))) k
  elimProp (⊤η t k) =
    isProp→PathP (λ k → isPropD (⊤η t k)) (elimProp t) dtt k
  elimProp (pair-nat a b f k) =
    isProp→PathP (λ k → isPropD (pair-nat a b f k))
      (d⟪⟫ (dpair (elimProp a) (elimProp b)) (λ i → elimProp (f i)))
      (dpair (d⟪⟫ (elimProp a) (λ i → elimProp (f i)))
             (d⟪⟫ (elimProp b) (λ i → elimProp (f i)))) k
  elimProp (fst-nat t f k) =
    isProp→PathP (λ k → isPropD (fst-nat t f k))
      (d⟪⟫ (dfst (elimProp t)) (λ i → elimProp (f i)))
      (dfst (d⟪⟫ (elimProp t) (λ i → elimProp (f i)))) k
  elimProp (snd-nat t f k) =
    isProp→PathP (λ k → isPropD (snd-nat t f k))
      (d⟪⟫ (dsnd (elimProp t)) (λ i → elimProp (f i)))
      (dsnd (d⟪⟫ (elimProp t) (λ i → elimProp (f i)))) k
  elimProp (×β₁ a b k) =
    isProp→PathP (λ k → isPropD (×β₁ a b k))
      (dfst (dpair (elimProp a) (elimProp b))) (elimProp a) k
  elimProp (×β₂ a b k) =
    isProp→PathP (λ k → isPropD (×β₂ a b k))
      (dsnd (dpair (elimProp a) (elimProp b))) (elimProp b) k
  elimProp (×η t k) =
    isProp→PathP (λ k → isPropD (×η t k))
      (dpair (dfst (elimProp t)) (dsnd (elimProp t))) (elimProp t) k
  elimProp (lam-nat t f f↑ f↑l f↑r k) =
    isProp→PathP (λ k → isPropD (lam-nat t f f↑ f↑l f↑r k))
      (d⟪⟫ (dlam (elimProp t)) (λ i → elimProp (f i)))
      (dlam (d⟪⟫ (elimProp t) (λ i → elimProp (f↑ i)))) k
  elimProp (app-nat t u f k) =
    isProp→PathP (λ k → isPropD (app-nat t u f k))
      (d⟪⟫ (dapp (elimProp t) (elimProp u)) (λ i → elimProp (f i)))
      (dapp (d⟪⟫ (elimProp t) (λ i → elimProp (f i)))
            (d⟪⟫ (elimProp u) (λ i → elimProp (f i)))) k
  elimProp (⇒β t u f fl fr k) =
    isProp→PathP (λ k → isPropD (⇒β t u f fl fr k))
      (dapp (dlam (elimProp t)) (elimProp u))
      (d⟪⟫ (elimProp t) (λ i → elimProp (f i))) k
  elimProp (⇒η t k) =
    isProp→PathP (λ k → isPropD (⇒η t k))
      (dlam (dapp (d⟪⟫ (elimProp t) (λ j → dvar (inl j))) (dvar (inr tt))))
      (elimProp t) k
  elimProp (trunc t u p q k k') =
    isOfHLevel→isOfHLevelDep 2 (λ t → isProp→isSet (isPropD t))
      (elimProp t) (elimProp u)
      (cong elimProp p) (cong elimProp q) (trunc t u p q) k k'

-- the syntax is a cartesian multicategory: the clone laws are exactly
-- the path constructors
Syn : CartesianMulticategory ℓ-zero ℓ-zero (ℓ-suc ℓ-zero)
Syn .CartesianMulticategory.ob = Ty
Syn .CartesianMulticategory.MHom⟨_⟩[_,_] I Γ A = Tm I Γ A
Syn .CartesianMulticategory.var i = var i
Syn .CartesianMulticategory._⋆_ t f = t ⟪ f ⟫
Syn .CartesianMulticategory.⋆Var i f = ⟪⟫var i f
Syn .CartesianMulticategory.⋆Id t = ⟪⟫id t
Syn .CartesianMulticategory.⋆Assoc t f g = ⟪⟫⟪⟫ t f g
Syn .CartesianMulticategory.isSetMHom = trunc
