{-# OPTIONS --cubical --type-in-type #-}

module HyperDoc.Operational.Effects.Writer where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import HyperDoc.Algebra.Base
open import HyperDoc.Operational.Effects.Reduction
  using (Polynomial; ⟦_⟧; mapP)
open import HyperDoc.Operational.Effects.MonadicReduction

open Polynomial
open Functor
open NatTrans
open IsMonad

------------------------------------------------------------------------
-- The polynomial writer monad, using difference-list logs.
-- A shape d : ℕ → ℕ represents the accumulated log d 0.

WriterP : Polynomial
WriterP .Shape = ℕ → ℕ
WriterP .size _ = 1

writer-shape-isSet : isSet (Shape WriterP)
writer-shape-isSet = isSetΠ (λ _ → isSetℕ)

WriterT : hSet ℓ-zero → hSet ℓ-zero
WriterT = ⟦ WriterP ⟧Set writer-shape-isSet

η-writer : ∀ {X : hSet ℓ-zero} → ⟨ X ⟩ → ⟨ WriterT X ⟩
η-writer x = (λ n → n) , λ _ → x

μ-writer :
  ∀ {X : hSet ℓ-zero} → ⟨ WriterT (WriterT X) ⟩ → ⟨ WriterT X ⟩
μ-writer (m , k) =
  (λ n → m (fst (k zero) n)) , snd (k zero)

η-writer-natural :
  NatTrans (𝟙⟨ SET ℓ-zero ⟩) (⟦ WriterP ⟧Functor writer-shape-isSet)
η-writer-natural .N-ob X = η-writer {X = X}
η-writer-natural .N-hom f = refl

μ-writer-natural :
  NatTrans
    (funcComp
      (⟦ WriterP ⟧Functor writer-shape-isSet)
      (⟦ WriterP ⟧Functor writer-shape-isSet))
    (⟦ WriterP ⟧Functor writer-shape-isSet)
μ-writer-natural .N-ob X = μ-writer {X = X}
μ-writer-natural .N-hom f = refl

WriterMonad : IsMonad (⟦ WriterP ⟧Functor writer-shape-isSet)
WriterMonad .η = η-writer-natural
WriterMonad .μ = μ-writer-natural
WriterMonad .idl-μ =
  makeNatTransPathP F-rUnit refl
    (funExt λ X → funExt λ { (m , xs) → refl })
WriterMonad .idr-μ =
  makeNatTransPathP F-lUnit refl
    (funExt λ X → funExt λ { (m , xs) →
      ΣPathP
        ( refl
        , funExt λ i → cong xs (isContrFin1 .snd i)
        )
      })
WriterMonad .assoc-μ =
  makeNatTransPathP F-assoc refl
    (funExt λ X → funExt λ { (m , k) → refl })

------------------------------------------------------------------------
-- Writer signature and its algebra on every WriterT X

data WriterOp : Type where
  tell : ℕ → WriterOp

WriterΣ : Signature
WriterΣ .Op = WriterOp
WriterΣ .arity (tell n) = 1

Writer-alg : (X : hSet ℓ-zero) → IsAlg WriterΣ (WriterT X)
Writer-alg X (tell n) args =
  (λ k → n + fst (args zero) k) , snd (args zero)

map-writer-alg :
  ∀ {X Y : hSet ℓ-zero} (f : ⟨ X ⟩ → ⟨ Y ⟩) →
  IsAlgHom
    {M = record { Carrier = WriterT X ; interp = Writer-alg X }}
    {N = record { Carrier = WriterT Y ; interp = Writer-alg Y }}
    (mapP f)
map-writer-alg f (tell n) args = refl

μ-writer-alg :
  (X : hSet ℓ-zero) →
  IsAlgHom
    {M = record { Carrier = WriterT (WriterT X)
                ; interp = Writer-alg (WriterT X) }}
    {N = record { Carrier = WriterT X ; interp = Writer-alg X }}
    (μ-writer {X = X})
μ-writer-alg X (tell n) args = refl

------------------------------------------------------------------------
-- A concrete ↦E step

module WriterReduction =
  MonadicReduction
    WriterΣ WriterP writer-shape-isSet WriterMonad Writer-alg

VariableSet : hSet ℓ-zero
VariableSet = Unit , isSetUnit

module Example =
  WriterReduction.Terms
    map-writer-alg μ-writer-alg VariableSet

open Example

return : FreeOn WriterΣ Unit
return = inc tt

C : ⟦ ∂ WriterP ⟧ (FreeOn WriterΣ Unit)
C = ((2 +_) , zero) , λ ()

t : ⟨ WriterT TermX ⟩
t = C [ ops (tell 3) (λ _ → ops (tell 4) (λ _ → return)) ]

t′ : ⟨ WriterT TermX ⟩
t′ =
  effect-step C (tell 3)
    (λ _ → ops (tell 4) (λ _ → return))

C′ : ⟦ ∂ WriterP ⟧ (FreeOn WriterΣ Unit)
C′ = (fst t′ , zero) , λ ()

t″ : ⟨ WriterT TermX ⟩
t″ = effect-step C′ (tell 4) (λ _ → return)

t↦t′ : t ↦E t′
t↦t′ =
  effect C (tell 3)
    (λ _ → ops (tell 4) (λ _ → return))

t′↦t″ : t′ ↦E t″
t′↦t″ =
  subst (λ u → u ↦E t″) source≡t′
    (effect C′ (tell 4) (λ _ → return))
  where
  source≡t′ : C′ [ ops (tell 4) (λ _ → return) ] ≡ t′
  source≡t′ =
    ΣPathP
      ( refl
      , funExt λ i →
          sym
            (cong
              (snd (C′ [ ops (tell 4) (λ _ → return) ]))
              (isContrFin1 .snd i))
          ∙ cong (snd t′) (isContrFin1 .snd i)
      )

-- The observable logs are 2, then 2 + 3, then 2 + 3 + 4.
t-log  : fst t  0 ≡ 2
t′-log : fst t′ 0 ≡ 5
t″-log : fst t″ 0 ≡ 9
t-log  = refl
t′-log = refl
t″-log = refl
