{-

  The sum-free fragment, with a base type: the free cartesian
  multicategory with ι, ⊤, × and ⇒.

  Same presentation as Multicategory.Syntax — substitution is a
  constructor, so the clone laws are path constructors, and the
  extended environment of a binder rule is forded — but without sums,
  and with a base type so that normalization has something to say (with
  only ⊤, × and ⇒ every type is contractible and the language is
  degenerate).

  This is the fragment Multicategory.NbE normalizes.  Sums are excluded
  deliberately: +η makes normal forms case trees, and the fundamental
  theorem then needs commuting conversions, i.e. a cover semantics.

-}
module Multicategory.STLC where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit

open import Multicategory.Cartesian

data TyA : Type where
  ι    : TyA
  ⊤ᴬ   : TyA
  _×ᴬ_ : TyA → TyA → TyA
  _⇒ᴬ_ : TyA → TyA → TyA

infixr 5 _⇒ᴬ_
infixr 7 _×ᴬ_

CtxtA : Type → Type
CtxtA I = I → TyA

_,,ᴬ_ : {I : Type} → CtxtA I → TyA → CtxtA (I ⊎ Unit)
(Γ ,,ᴬ A) (inl i) = Γ i
(Γ ,,ᴬ A) (inr _) = A

infixl 5 _,,ᴬ_

data TmA : (I : Type) (Γ : CtxtA I) (A : TyA) → Type₁ where
  varA : {I : Type} {Γ : CtxtA I} (i : I) → TmA I Γ (Γ i)

  _⟨_⟩A : {I J : Type} {Γ : CtxtA I} {Δ : CtxtA J} {A : TyA}
    → TmA I Γ A → ((i : I) → TmA J Δ (Γ i)) → TmA J Δ A

  -- the clone laws
  ⟨⟩varA : {I J : Type} {Γ : CtxtA I} {Δ : CtxtA J}
    (i : I) (f : (i : I) → TmA J Δ (Γ i))
    → (varA i ⟨ f ⟩A) ≡ f i
  ⟨⟩idA : {I : Type} {Γ : CtxtA I} {A : TyA} (t : TmA I Γ A)
    → (t ⟨ varA ⟩A) ≡ t
  ⟨⟩⟨⟩A : {I J K : Type} {Γ : CtxtA I} {Δ : CtxtA J} {Θ : CtxtA K}
    {A : TyA} (t : TmA I Γ A)
    (f : (i : I) → TmA J Δ (Γ i)) (g : (j : J) → TmA K Θ (Δ j))
    → ((t ⟨ f ⟩A) ⟨ g ⟩A) ≡ (t ⟨ (λ i → f i ⟨ g ⟩A) ⟩A)

  -- unit
  ttA : {I : Type} {Γ : CtxtA I} → TmA I Γ ⊤ᴬ
  ⊤ηA : {I : Type} {Γ : CtxtA I} (t : TmA I Γ ⊤ᴬ) → t ≡ ttA

  -- products
  pairA : {I : Type} {Γ : CtxtA I} {A B : TyA}
    → TmA I Γ A → TmA I Γ B → TmA I Γ (A ×ᴬ B)
  fstA : {I : Type} {Γ : CtxtA I} {A B : TyA}
    → TmA I Γ (A ×ᴬ B) → TmA I Γ A
  sndA : {I : Type} {Γ : CtxtA I} {A B : TyA}
    → TmA I Γ (A ×ᴬ B) → TmA I Γ B

  pair-natA : {I J : Type} {Γ : CtxtA I} {Δ : CtxtA J} {A B : TyA}
    (a : TmA I Γ A) (b : TmA I Γ B) (f : (i : I) → TmA J Δ (Γ i))
    → (pairA a b ⟨ f ⟩A) ≡ pairA (a ⟨ f ⟩A) (b ⟨ f ⟩A)
  fst-natA : {I J : Type} {Γ : CtxtA I} {Δ : CtxtA J} {A B : TyA}
    (t : TmA I Γ (A ×ᴬ B)) (f : (i : I) → TmA J Δ (Γ i))
    → (fstA t ⟨ f ⟩A) ≡ fstA (t ⟨ f ⟩A)
  snd-natA : {I J : Type} {Γ : CtxtA I} {Δ : CtxtA J} {A B : TyA}
    (t : TmA I Γ (A ×ᴬ B)) (f : (i : I) → TmA J Δ (Γ i))
    → (sndA t ⟨ f ⟩A) ≡ sndA (t ⟨ f ⟩A)

  ×β₁A : {I : Type} {Γ : CtxtA I} {A B : TyA}
    (a : TmA I Γ A) (b : TmA I Γ B) → fstA (pairA a b) ≡ a
  ×β₂A : {I : Type} {Γ : CtxtA I} {A B : TyA}
    (a : TmA I Γ A) (b : TmA I Γ B) → sndA (pairA a b) ≡ b
  ×ηA : {I : Type} {Γ : CtxtA I} {A B : TyA}
    (t : TmA I Γ (A ×ᴬ B)) → pairA (fstA t) (sndA t) ≡ t

  -- functions
  lamA : {I : Type} {Γ : CtxtA I} {A B : TyA}
    → TmA (I ⊎ Unit) (Γ ,,ᴬ A) B → TmA I Γ (A ⇒ᴬ B)
  appA : {I : Type} {Γ : CtxtA I} {A B : TyA}
    → TmA I Γ (A ⇒ᴬ B) → TmA I Γ A → TmA I Γ B

  lam-natA : {I J : Type} {Γ : CtxtA I} {Δ : CtxtA J} {A B : TyA}
    (t : TmA (I ⊎ Unit) (Γ ,,ᴬ A) B) (f : (i : I) → TmA J Δ (Γ i))
    (f↑ : (i : I ⊎ Unit) → TmA (J ⊎ Unit) (Δ ,,ᴬ A) ((Γ ,,ᴬ A) i))
    (f↑l : (i : I) → f↑ (inl i) ≡ (f i ⟨ (λ j → varA (inl j)) ⟩A))
    (f↑r : f↑ (inr tt) ≡ varA (inr tt))
    → (lamA t ⟨ f ⟩A) ≡ lamA (t ⟨ f↑ ⟩A)
  app-natA : {I J : Type} {Γ : CtxtA I} {Δ : CtxtA J} {A B : TyA}
    (t : TmA I Γ (A ⇒ᴬ B)) (u : TmA I Γ A) (f : (i : I) → TmA J Δ (Γ i))
    → (appA t u ⟨ f ⟩A) ≡ appA (t ⟨ f ⟩A) (u ⟨ f ⟩A)

  ⇒βA : {I : Type} {Γ : CtxtA I} {A B : TyA}
    (t : TmA (I ⊎ Unit) (Γ ,,ᴬ A) B) (u : TmA I Γ A)
    (f : (i : I ⊎ Unit) → TmA I Γ ((Γ ,,ᴬ A) i))
    (fl : (i : I) → f (inl i) ≡ varA i) (fr : f (inr tt) ≡ u)
    → appA (lamA t) u ≡ (t ⟨ f ⟩A)
  ⇒ηA : {I : Type} {Γ : CtxtA I} {A B : TyA} (t : TmA I Γ (A ⇒ᴬ B))
    → lamA (appA (t ⟨ (λ j → varA (inl j)) ⟩A) (varA (inr tt))) ≡ t

  truncA : {I : Type} {Γ : CtxtA I} {A : TyA} → isSet (TmA I Γ A)

infixl 8 _⟨_⟩A

-- eliminating into a prop-valued motive: all fourteen path
-- constructors are discharged at once
module ElimPropA {ℓ}
  {D : {I : Type} {Γ : CtxtA I} {A : TyA} → TmA I Γ A → Type ℓ}
  (isPropD : {I : Type} {Γ : CtxtA I} {A : TyA} (t : TmA I Γ A)
    → isProp (D t))
  (dvar : {I : Type} {Γ : CtxtA I} (i : I) → D (varA {Γ = Γ} i))
  (d⟨⟩ : {I J : Type} {Γ : CtxtA I} {Δ : CtxtA J} {A : TyA}
    {t : TmA I Γ A} {f : (i : I) → TmA J Δ (Γ i)}
    → D t → ((i : I) → D (f i)) → D (t ⟨ f ⟩A))
  (dtt : {I : Type} {Γ : CtxtA I} → D (ttA {I} {Γ}))
  (dpair : {I : Type} {Γ : CtxtA I} {A B : TyA}
    {a : TmA I Γ A} {b : TmA I Γ B} → D a → D b → D (pairA a b))
  (dfst : {I : Type} {Γ : CtxtA I} {A B : TyA}
    {t : TmA I Γ (A ×ᴬ B)} → D t → D (fstA t))
  (dsnd : {I : Type} {Γ : CtxtA I} {A B : TyA}
    {t : TmA I Γ (A ×ᴬ B)} → D t → D (sndA t))
  (dlam : {I : Type} {Γ : CtxtA I} {A B : TyA}
    {t : TmA (I ⊎ Unit) (Γ ,,ᴬ A) B} → D t → D (lamA t))
  (dapp : {I : Type} {Γ : CtxtA I} {A B : TyA}
    {t : TmA I Γ (A ⇒ᴬ B)} {u : TmA I Γ A} → D t → D u → D (appA t u))
  where

  elimProp : {I : Type} {Γ : CtxtA I} {A : TyA} (t : TmA I Γ A) → D t
  elimProp (varA i) = dvar i
  elimProp (t ⟨ f ⟩A) = d⟨⟩ (elimProp t) (λ i → elimProp (f i))
  elimProp ttA = dtt
  elimProp (pairA a b) = dpair (elimProp a) (elimProp b)
  elimProp (fstA t) = dfst (elimProp t)
  elimProp (sndA t) = dsnd (elimProp t)
  elimProp (lamA t) = dlam (elimProp t)
  elimProp (appA t u) = dapp (elimProp t) (elimProp u)
  elimProp (⟨⟩varA i f k) =
    isProp→PathP (λ k → isPropD (⟨⟩varA i f k))
      (d⟨⟩ (dvar i) (λ i → elimProp (f i))) (elimProp (f i)) k
  elimProp (⟨⟩idA t k) =
    isProp→PathP (λ k → isPropD (⟨⟩idA t k))
      (d⟨⟩ (elimProp t) (λ i → dvar i)) (elimProp t) k
  elimProp (⟨⟩⟨⟩A t f g k) =
    isProp→PathP (λ k → isPropD (⟨⟩⟨⟩A t f g k))
      (d⟨⟩ (d⟨⟩ (elimProp t) (λ i → elimProp (f i)))
           (λ j → elimProp (g j)))
      (d⟨⟩ (elimProp t)
           (λ i → d⟨⟩ (elimProp (f i)) (λ j → elimProp (g j)))) k
  elimProp (⊤ηA t k) =
    isProp→PathP (λ k → isPropD (⊤ηA t k)) (elimProp t) dtt k
  elimProp (pair-natA a b f k) =
    isProp→PathP (λ k → isPropD (pair-natA a b f k))
      (d⟨⟩ (dpair (elimProp a) (elimProp b)) (λ i → elimProp (f i)))
      (dpair (d⟨⟩ (elimProp a) (λ i → elimProp (f i)))
             (d⟨⟩ (elimProp b) (λ i → elimProp (f i)))) k
  elimProp (fst-natA t f k) =
    isProp→PathP (λ k → isPropD (fst-natA t f k))
      (d⟨⟩ (dfst (elimProp t)) (λ i → elimProp (f i)))
      (dfst (d⟨⟩ (elimProp t) (λ i → elimProp (f i)))) k
  elimProp (snd-natA t f k) =
    isProp→PathP (λ k → isPropD (snd-natA t f k))
      (d⟨⟩ (dsnd (elimProp t)) (λ i → elimProp (f i)))
      (dsnd (d⟨⟩ (elimProp t) (λ i → elimProp (f i)))) k
  elimProp (×β₁A a b k) =
    isProp→PathP (λ k → isPropD (×β₁A a b k))
      (dfst (dpair (elimProp a) (elimProp b))) (elimProp a) k
  elimProp (×β₂A a b k) =
    isProp→PathP (λ k → isPropD (×β₂A a b k))
      (dsnd (dpair (elimProp a) (elimProp b))) (elimProp b) k
  elimProp (×ηA t k) =
    isProp→PathP (λ k → isPropD (×ηA t k))
      (dpair (dfst (elimProp t)) (dsnd (elimProp t))) (elimProp t) k
  elimProp (lam-natA t f f↑ f↑l f↑r k) =
    isProp→PathP (λ k → isPropD (lam-natA t f f↑ f↑l f↑r k))
      (d⟨⟩ (dlam (elimProp t)) (λ i → elimProp (f i)))
      (dlam (d⟨⟩ (elimProp t) (λ i → elimProp (f↑ i)))) k
  elimProp (app-natA t u f k) =
    isProp→PathP (λ k → isPropD (app-natA t u f k))
      (d⟨⟩ (dapp (elimProp t) (elimProp u)) (λ i → elimProp (f i)))
      (dapp (d⟨⟩ (elimProp t) (λ i → elimProp (f i)))
            (d⟨⟩ (elimProp u) (λ i → elimProp (f i)))) k
  elimProp (⇒βA t u f fl fr k) =
    isProp→PathP (λ k → isPropD (⇒βA t u f fl fr k))
      (dapp (dlam (elimProp t)) (elimProp u))
      (d⟨⟩ (elimProp t) (λ i → elimProp (f i))) k
  elimProp (⇒ηA t k) =
    isProp→PathP (λ k → isPropD (⇒ηA t k))
      (dlam (dapp (d⟨⟩ (elimProp t) (λ j → dvar (inl j))) (dvar (inr tt))))
      (elimProp t) k
  elimProp (truncA t u p q k k') =
    isOfHLevel→isOfHLevelDep 2 (λ t → isProp→isSet (isPropD t))
      (elimProp t) (elimProp u)
      (cong elimProp p) (cong elimProp q) (truncA t u p q) k k'

-- the fragment is a cartesian multicategory too
SynA : CartesianMulticategory ℓ-zero ℓ-zero (ℓ-suc ℓ-zero)
SynA .CartesianMulticategory.ob = TyA
SynA .CartesianMulticategory.MHom⟨_⟩[_,_] I Γ A = TmA I Γ A
SynA .CartesianMulticategory.var i = varA i
SynA .CartesianMulticategory._⋆_ t f = t ⟨ f ⟩A
SynA .CartesianMulticategory.⋆Var i f = ⟨⟩varA i f
SynA .CartesianMulticategory.⋆Id t = ⟨⟩idA t
SynA .CartesianMulticategory.⋆Assoc t f g = ⟨⟩⟨⟩A t f g
SynA .CartesianMulticategory.isSetMHom = truncA
