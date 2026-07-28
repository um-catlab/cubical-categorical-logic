{-# OPTIONS --cubical --type-in-type #-}

module HyperDoc.Operational.Effects.MonadicReduction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.ExtensionSystem
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import HyperDoc.Algebra.Base
  using
    ( Signature; Op; arity
    ; IsAlg; Alg; Carrier; interp; IsAlgHom
    ; FreeOn; inc; ops
    )
open import HyperDoc.Operational.Effects.Reduction
  using (Polynomial; ⟦_⟧; mapP)

open Polynomial

-----------------------------------------------------------------------
-- The derivative of a polynomial

∂ : Polynomial → Polynomial
∂ P .Shape = Σ[ s ∈ Shape P ] Fin (size P s)
∂ P .size (s , i) = predℕ (size P s)

-- Insert a distinguished element at position i.  The remaining n
-- elements are exactly the positions of the derivative polynomial.
insertAt :
  ∀ {n : ℕ}{X} →
  Fin (suc n) → X → (Fin n → X) → Fin (suc n) → X
insertAt zero x xs zero = x
insertAt zero x xs (suc j) = xs j
insertAt (suc i) x xs zero = xs zero
insertAt (suc i) x xs (suc j) =
  insertAt i x (λ k → xs (suc k)) j

plugAt :
  ∀ {n X} →
  (i : Fin n) → X → (Fin (predℕ n) → X) → Fin n → X
plugAt {suc n} i = insertAt i

_[_] :
  ∀ {P : Polynomial} {X : Type} → ⟦ ∂ P ⟧ X → X → ⟦ P ⟧ X
_[_] ((s , i) , xs) x = s , plugAt i x xs

map∂ :
  ∀ {P : Polynomial} {X Y : Type} →
  (X → Y) → ⟦ ∂ P ⟧ X → ⟦ ∂ P ⟧ Y
map∂ = mapP

map-insertAt :
  ∀ {n X Y}
    (f : X → Y) (i : Fin (suc n)) x xs →
  (λ j → f (insertAt i x xs j))
    ≡ insertAt i (f x) (λ j → f (xs j))
map-insertAt f zero x xs = refl
map-insertAt f (suc i) x xs =
  funExt λ
    { zero → refl
    ; (suc j) → funExt⁻ (map-insertAt f i x (λ k → xs (suc k))) j
    }

map-plugAt :
  ∀ {n X Y} (f : X → Y) (i : Fin n) x xs →
  (λ j → f (plugAt i x xs j))
    ≡ plugAt i (f x) (λ j → f (xs j))
map-plugAt {suc n} f i = map-insertAt f i

map-plug :
  ∀ {P : Polynomial} {X Y : Type}
    (f : X → Y) (C : ⟦ ∂ P ⟧ X) x →
  mapP f (C [ x ]) ≡ (map∂ f C) [ f x ]
map-plug f ((s , i) , xs) x =
  ΣPathP (refl , map-plugAt f i x xs)

map∂-comp :
  ∀ {P : Polynomial} {X Y Z : Type}
    (f : X → Y) (g : Y → Z) C →
  map∂ {P = P} g (map∂ f C) ≡ map∂ (λ x → g (f x)) C
map∂-comp f g ((s , i) , xs) = refl

------------------------------------------------------------------------
-- Section 3: monadic reduction

⟦_⟧Set :
  (P : Polynomial) → isSet (Shape P) →
  hSet ℓ-zero → hSet ℓ-zero
⟦ P ⟧Set shape-isSet X =
  ⟦ P ⟧ ⟨ X ⟩ ,
  isSetΣ shape-isSet (λ _ → isSetΠ (λ _ → X .snd))

⟦_⟧Functor :
  (P : Polynomial) → (shape-isSet : isSet (Shape P)) →
  Functor (SET ℓ-zero) (SET ℓ-zero)
⟦ P ⟧Functor shape-isSet .Functor.F-ob = ⟦ P ⟧Set shape-isSet
⟦ P ⟧Functor shape-isSet .Functor.F-hom = mapP
⟦ P ⟧Functor shape-isSet .Functor.F-id =
  funExt λ { (s , xs) → refl }
⟦ P ⟧Functor shape-isSet .Functor.F-seq f g =
  funExt λ { (s , xs) → refl }

module MonadicReduction
  (Σ : Signature)
  (P : Polynomial)
  (shape-isSet : isSet (Shape P))
  (monad : IsMonad (⟦ P ⟧Functor shape-isSet))
  (T-alg : (X : hSet ℓ-zero) → IsAlg Σ (⟦ P ⟧Set shape-isSet X))
  where

  T : hSet ℓ-zero → hSet ℓ-zero
  T = ⟦ P ⟧Set shape-isSet

  MonadP : Monad (SET ℓ-zero)
  MonadP = ⟦ P ⟧Functor shape-isSet , monad

  M : ExtensionSystemFor (SET ℓ-zero) T
  M = Monad→ExtensionSystem (SET ℓ-zero) MonadP .snd

  open ExtensionSystemFor M

  TAlg : hSet ℓ-zero → Alg Σ
  TAlg X .Carrier = T X
  TAlg X .interp = T-alg X

  alg : (X : hSet ℓ-zero) → IsAlg Σ (T X)
  alg = T-alg

  μ : ∀ {X} → ⟨ T (T X) ⟩ → ⟨ T X ⟩
  μ {X} =
    bind {a = T X} {b = X}
      (Category.id (SET ℓ-zero) {x = T X})

  bind-polynomial :
    ∀ {X Y : hSet ℓ-zero} (f : ⟨ X ⟩ → ⟨ T Y ⟩) t →
    bind {a = X} {b = Y} f t ≡ μ {X = Y} (mapP f t)
  bind-polynomial {X} {Y} f t = refl

  module _
    (map-alg :
      ∀ {X Y : hSet ℓ-zero} (f : ⟨ X ⟩ → ⟨ Y ⟩) →
      IsAlgHom {M = TAlg X} {N = TAlg Y} (mapP f))
    (μ-alg :
      ∀ (X : hSet ℓ-zero) →
      IsAlgHom {M = TAlg (T X)} {N = TAlg X}
        (NatTrans.N-ob (IsMonad.μ monad) X))
    where

    bind-alg :
      ∀ {X Y : hSet ℓ-zero}
        (f : ⟨ X ⟩ → ⟨ T Y ⟩)
        (o : Op Σ)
        (args : Fin (arity Σ o) → ⟨ T X ⟩) →
      bind {a = X} {b = Y} f (alg X o args)
        ≡ alg Y o (λ i → bind {a = X} {b = Y} f (args i))
    bind-alg {X} {Y} f o args =
      bind-polynomial {X = X} {Y = Y} f (alg X o args)
      ∙ cong (μ {X = Y})
          (map-alg {X = X} {Y = T Y} f o args)
      ∙ μ-alg Y o (λ i → mapP f (args i))
      ∙ cong (alg Y o)
        (funExt λ i →
          sym (bind-polynomial {X = X} {Y = Y} f (args i)))

    bind-μ :
      ∀ {X Y : hSet ℓ-zero} (f : ⟨ X ⟩ → ⟨ T Y ⟩)
        (t : ⟨ T (T X) ⟩) →
      bind {a = X} {b = Y} f (μ {X = X} t)
        ≡ μ {X = Y}
          (mapP (bind {a = X} {b = Y} f) t)
    bind-μ {X} {Y} f t =
      cong (λ h → h t)
        (bind-comp
          {X} {Y} {f} {T X}
          {Category.id (SET ℓ-zero) {x = T X}})
      ∙ bind-polynomial {X = T X} {Y = Y}
          (bind {a = X} {b = Y} f) t


    module Terms
      (X : hSet ℓ-zero)
      (term-isSet : isSet (FreeOn Σ ⟨ X ⟩))
      where

      TermX : hSet ℓ-zero
      TermX = FreeOn Σ ⟨ X ⟩ , term-isSet

      -- Figure 7.
      effect-step :
        ⟦ ∂ P ⟧ (FreeOn Σ ⟨ X ⟩) →
        (o : Op Σ) →
        (Fin (arity Σ o) → FreeOn Σ ⟨ X ⟩) →
        ⟨ T TermX ⟩
      effect-step C o args =
        μ {X = TermX} ((map∂ (η {a = TermX}) C)
          [ alg TermX o (λ i → η {a = TermX} (args i)) ])

      data _↦E_ : ⟨ T TermX ⟩ → ⟨ T TermX ⟩ → Type where
        effect :
          ∀ (C : ⟦ ∂ P ⟧ (FreeOn Σ ⟨ X ⟩))
            (o : Op Σ)
            (args : Fin (arity Σ o) → FreeOn Σ ⟨ X ⟩) →
          (C [ ops o args ]) ↦E effect-step C o args

      eval : FreeOn Σ ⟨ X ⟩ → ⟨ T X ⟩
      eval (inc x)      = η {a = X} x
      eval (ops o args) = alg X o (λ i → eval (args i))

      eval† : ⟨ T TermX ⟩ → ⟨ T X ⟩
      eval† = bind {a = TermX} {b = X} eval

      sound : ∀ {t t′ : ⟨ T TermX ⟩} → t ↦E t′ → eval† t ≡ eval† t′
      sound (effect C o args) =
        bind-polynomial {X = TermX} {Y = X}
          eval (C [ ops o args ])
        ∙ cong (μ {X = X}) (sym inside)
        ∙ sym (bind-μ {X = TermX} {Y = X} eval
          ((map∂ (η {a = TermX}) C)
            [ alg TermX o (λ i → η {a = TermX} (args i)) ]))
        where
        operation :
          bind {a = TermX} {b = X} eval
            (alg TermX o (λ i → η {a = TermX} (args i)))
            ≡ eval (ops o args)
        operation =
          bind-alg {X = TermX} {Y = X} eval o
            (λ i → η {a = TermX} (args i))
          ∙ cong (alg X o)
            (funExt λ i →
              funExt⁻
                (bind-l {TermX} {X} {eval})
                (args i))

        contexts :
          map∂ (bind {a = TermX} {b = X} eval)
            (map∂ (η {a = TermX}) C)
            ≡ map∂ eval C
        contexts =
          map∂-comp (η {a = TermX})
            (bind {a = TermX} {b = X} eval) C
          ∙ cong (λ f → map∂ f C)
            (bind-l {TermX} {X} {eval})

        inside :
          mapP eval (C [ ops o args ])
            ≡
          mapP (bind {a = TermX} {b = X} eval)
            ((map∂ (η {a = TermX}) C)
              [ alg TermX o (λ i → η {a = TermX} (args i)) ])
        inside =
          map-plug eval C (ops o args)
          ∙ cong₂ (λ C′ x → _[_] {P = P} C′ x)
              (sym contexts) (sym operation)
          ∙ sym (map-plug (bind {a = TermX} {b = X} eval)
            (map∂ (η {a = TermX}) C)
            (alg TermX o (λ i → η {a = TermX} (args i))))
