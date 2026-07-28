{-# OPTIONS --cubical --type-in-type #-}

module HyperDoc.Operational.Effects.MonadicReductionSplit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Monad.ExtensionSystem
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.FinData
import Cubical.HITs.SetQuotients.Base as SQ
import Cubical.HITs.SetQuotients.Properties as SQ

open import HyperDoc.Algebra.Base
  using
    ( Signature; Op; arity
    ; IsAlg; Alg; Carrier; interp; IsAlgHom
    ; FreeOn; inc; ops; trunc
    )
open import HyperDoc.Operational.Effects.Reduction
  using (Polynomial; ⟦_⟧; mapP; Relation)
import HyperDoc.Operational.Effects.Reduction as OldReduction
open import HyperDoc.Operational.Effects.MonadicReduction
  using (∂; _[_]; map∂; map-plug; map∂-comp)

open Polynomial
open Functor

module Quotient
  (P : Polynomial)
  (R : Relation P)
  (R-map :
    ∀ {X Y : hSet ℓ-zero} (f : ⟨ X ⟩ → ⟨ Y ⟩) u v →
    ⟨ R X u v ⟩ →
    ⟨ R Y (mapP f u) (mapP f v) ⟩)
  where

  T : hSet ℓ-zero → hSet ℓ-zero
  T X =
    (⟦ P ⟧ ⟨ X ⟩ SQ./ λ u v → ⟨ R X u v ⟩) ,
    SQ.squash/

  quoteT : ∀ {X : hSet ℓ-zero} → ⟦ P ⟧ ⟨ X ⟩ → ⟨ T X ⟩
  quoteT t = SQ.[ t ]

  mapT :
    ∀ {X Y : hSet ℓ-zero} →
    (⟨ X ⟩ → ⟨ Y ⟩) → ⟨ T X ⟩ → ⟨ T Y ⟩
  mapT {X} {Y} f =
    SQ.rec SQ.squash/
      (λ t → quoteT (mapP f t))
      (λ u v r → SQ.eq/ _ _ (R-map f u v r))

  mapT-quoteT :
    ∀ {X Y : hSet ℓ-zero} (f : ⟨ X ⟩ → ⟨ Y ⟩) t →
    mapT f (quoteT t) ≡ quoteT (mapP f t)
  mapT-quoteT f t = refl

  QuotientFunctor : Functor (SET ℓ-zero) (SET ℓ-zero)
  QuotientFunctor .F-ob = T
  QuotientFunctor .F-hom = mapT
  QuotientFunctor .F-id =
    funExt (SQ.elimProp
      (λ _ → SQ.squash/ _ _)
      (λ _ → refl))
  QuotientFunctor .F-seq f g =
    funExt (SQ.elimProp
      (λ _ → SQ.squash/ _ _)
      (λ _ → refl))

module SetQuotientMonadicReduction
  (Σ : Signature)
  (P : Polynomial)
  (R : Relation P)
  (R-map :
    ∀ {X Y : hSet ℓ-zero} (f : ⟨ X ⟩ → ⟨ Y ⟩) u v →
    ⟨ R X u v ⟩ →
    ⟨ R Y (mapP f u) (mapP f v) ⟩)
  where

  module QuotientP = Quotient P R R-map
  open QuotientP public

  module _
    (monad : IsMonad QuotientFunctor)
    (T-alg : (X : hSet ℓ-zero) → IsAlg Σ (T X))
    where

    MonadT : Monad (SET ℓ-zero)
    MonadT = QuotientFunctor , monad

    M : ExtensionSystemFor (SET ℓ-zero) T
    M = Monad→ExtensionSystem (SET ℓ-zero) MonadT .snd

    open ExtensionSystemFor M

    TAlg : hSet ℓ-zero → Alg Σ
    TAlg X .Carrier = T X
    TAlg X .interp = T-alg X

    alg : (X : hSet ℓ-zero) → IsAlg Σ (T X)
    alg = T-alg

    μ : ∀ {X} → ⟨ T (T X) ⟩ → ⟨ T X ⟩
    μ {X} = NatTrans.N-ob (IsMonad.μ monad) X

    joinK-monad :
      ∀ {X} (t : ⟨ T (T X) ⟩) →
      bind {a = T X} {b = X}
        (Category.id (SET ℓ-zero) {x = T X}) t
        ≡ μ {X = X} t
    joinK-monad {X} t =
      cong (NatTrans.N-ob (IsMonad.μ monad) X)
        (funExt⁻ (QuotientFunctor .F-id) t)

    bind-map :
      ∀ {X Y : hSet ℓ-zero} (f : ⟨ X ⟩ → ⟨ T Y ⟩) t →
      bind {a = X} {b = Y} f t ≡ μ {X = Y} (mapT f t)
    bind-map f t = refl

    bind-quoteT :
      ∀ {X Y : hSet ℓ-zero} (f : ⟨ X ⟩ → ⟨ T Y ⟩) t →
      bind {a = X} {b = Y} f (quoteT t)
        ≡ μ {X = Y} (quoteT (mapP f t))
    bind-quoteT f t = refl

    module _
      (map-alg :
        ∀ {X Y : hSet ℓ-zero} (f : ⟨ X ⟩ → ⟨ Y ⟩) →
        IsAlgHom {M = TAlg X} {N = TAlg Y} (mapT f))
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
        refl
        ∙ cong (μ {X = Y}) (map-alg f o args)
        ∙ μ-alg Y o (λ i → mapT f (args i))
        ∙ cong (alg Y o) (funExt λ _ → refl)

      bind-μ :
        ∀ {X Y : hSet ℓ-zero} (f : ⟨ X ⟩ → ⟨ T Y ⟩)
          (t : ⟨ T (T X) ⟩) →
        bind {a = X} {b = Y} f (μ {X = X} t)
          ≡ μ {X = Y} (mapT (bind {a = X} {b = Y} f) t)
      bind-μ {X} {Y} f t =
        cong (bind {a = X} {b = Y} f) (sym (joinK-monad t))
        ∙ cong (λ h → h t)
            (bind-comp
              {X} {Y} {f} {T X}
              {Category.id (SET ℓ-zero) {x = T X}})
        ∙ bind-map {X = T X} {Y = Y}
            (bind {a = X} {b = Y} f) t

      module Terms
        (X : hSet ℓ-zero)
        (choice : ⟨ T (FreeOn Σ ⟨ X ⟩ , trunc) ⟩ →
                  ⟦ P ⟧ (FreeOn Σ ⟨ X ⟩))
        (quoteT-choice :
          (u : ⟨ T (FreeOn Σ ⟨ X ⟩ , trunc) ⟩) →
          quoteT {X = FreeOn Σ ⟨ X ⟩ , trunc} (choice u) ≡ u)
        where

        TermX : hSet ℓ-zero
        TermX = FreeOn Σ ⟨ X ⟩ , trunc

        effect-step :
          ⟦ ∂ P ⟧ (FreeOn Σ ⟨ X ⟩) →
          (o : Op Σ) →
          (Fin (arity Σ o) → FreeOn Σ ⟨ X ⟩) →
          ⟦ P ⟧ (FreeOn Σ ⟨ X ⟩)
        effect-step C o args =
          choice
            (μ {X = TermX}
              (quoteT {X = T TermX}
                ((map∂ (η {a = TermX}) C)
                  [ alg TermX o
                      (λ i → η {a = TermX} (args i)) ])))

        data _↦E_ :
          ⟦ P ⟧ (FreeOn Σ ⟨ X ⟩) →
          ⟦ P ⟧ (FreeOn Σ ⟨ X ⟩) → Type where
          effect :
            ∀ (C : ⟦ ∂ P ⟧ (FreeOn Σ ⟨ X ⟩))
              (o : Op Σ)
              (args : Fin (arity Σ o) → FreeOn Σ ⟨ X ⟩) →
            (C [ ops o args ]) ↦E effect-step C o args

        eval : FreeOn Σ ⟨ X ⟩ → ⟨ T X ⟩
        eval (inc x) = η {a = X} x
        eval (ops o args) = alg X o (λ i → eval (args i))
        eval (trunc t t′ p r i j) =
          T X .snd
            (eval t) (eval t′)
            (cong eval p) (cong eval r) i j

        eval† : ⟦ P ⟧ (FreeOn Σ ⟨ X ⟩) → ⟨ T X ⟩
        eval† t =
          bind {a = TermX} {b = X} eval
            (quoteT {X = TermX} t)

        sound : ∀ {t t′} → t ↦E t′ → eval† t ≡ eval† t′
        sound (effect C o args) = result
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
                  funExt⁻ (bind-l {TermX} {X} {eval}) (args i))

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
                [ alg TermX o
                    (λ i → η {a = TermX} (args i)) ])
          inside =
            map-plug eval C (ops o args)
            ∙ cong₂ (λ C′ x → _[_] {P = P} C′ x)
                (sym contexts) (sym operation)
            ∙ sym
                (map-plug (bind {a = TermX} {b = X} eval)
                  (map∂ (η {a = TermX}) C)
                  (alg TermX o
                    (λ i → η {a = TermX} (args i))))

          redex :
            ⟨ T (T TermX) ⟩
          redex =
            quoteT {X = T TermX}
              ((map∂ (η {a = TermX}) C)
                [ alg TermX o
                    (λ i → η {a = TermX} (args i)) ])

          result :
            eval† (C [ ops o args ]) ≡ eval† (effect-step C o args)
          result =
            bind-quoteT {X = TermX} {Y = X}
              eval (C [ ops o args ])
            ∙ cong (μ {X = X}) (cong quoteT inside)
            ∙ sym (bind-μ {X = TermX} {Y = X} eval redex)
            ∙ sym
                (cong (bind {a = TermX} {b = X} eval)
                  (quoteT-choice (μ {X = TermX} redex)))

------------------------------------------------------------------------
-- Extension-system presentation, used before choosing a fixed term set

module MonadicReductionSplit
  (Σ : Signature)
  (P : Polynomial)
  (R : Relation P)
  (T/R : hSet ℓ-zero → hSet ℓ-zero)
  (quoteT : (X : hSet ℓ-zero) → ⟦ P ⟧ ⟨ X ⟩ → ⟨ T/R X ⟩)
  (quoteT-resp :
    ∀ X u v → ⟨ R X u v ⟩ → quoteT X u ≡ quoteT X v)
  (monad : ExtensionSystemFor (SET ℓ-zero) T/R)
  (T/R-alg : (X : hSet ℓ-zero) → IsAlg Σ (T/R X))
  where

  open ExtensionSystemFor monad

  μ : ∀ {X} → ⟨ T/R (T/R X) ⟩ → ⟨ T/R X ⟩
  μ = bind (Category.id (SET ℓ-zero))

  module Terms
    (X : hSet ℓ-zero)
    (choice : ⟨ T/R (FreeOn Σ ⟨ X ⟩ , trunc) ⟩ →
              ⟦ P ⟧ (FreeOn Σ ⟨ X ⟩))
    (quoteT-choice :
      (u : ⟨ T/R (FreeOn Σ ⟨ X ⟩ , trunc) ⟩) →
      quoteT (FreeOn Σ ⟨ X ⟩ , trunc) (choice u) ≡ u)
    where

    TermX : hSet ℓ-zero
    TermX = FreeOn Σ ⟨ X ⟩ , trunc

    effect-step :
      ⟦ ∂ P ⟧ (FreeOn Σ ⟨ X ⟩) →
      (o : Op Σ) →
      (Fin (arity Σ o) → FreeOn Σ ⟨ X ⟩) →
      ⟦ P ⟧ (FreeOn Σ ⟨ X ⟩)
    effect-step C o args =
      choice
        (μ {X = TermX}
          (quoteT (T/R TermX)
            ((map∂ (η {a = TermX}) C)
              [ T/R-alg TermX o
                  (λ i → η {a = TermX} (args i)) ])))

    data _↦E_ :
      ⟦ P ⟧ (FreeOn Σ ⟨ X ⟩) →
      ⟦ P ⟧ (FreeOn Σ ⟨ X ⟩) → Type where
      effect :
        ∀ (C : ⟦ ∂ P ⟧ (FreeOn Σ ⟨ X ⟩))
          (o : Op Σ)
          (args : Fin (arity Σ o) → FreeOn Σ ⟨ X ⟩) →
        (C [ ops o args ]) ↦E effect-step C o args
