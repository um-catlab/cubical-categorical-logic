{-

  Propositional displayed ω-types and ω+-types.

  equations and section equations are automatic.

-}

module Cubical.Data.StepIndexedSet.Displayed.Propositions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.StepIndexedSet.Base
open import Cubical.Data.StepIndexedSet.Displayed.Base

open ωType
open ωTypeᴰ
open ωChain
open ωChainᴰ
open ωHom
open ωHomᴰ
open ω+Type
open ω+Typeᴰ
open ω+Hom
open ω+Homᴰ

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

isωPropᴰ : {X : ωType ℓ} (Xᴰ : ωTypeᴰ X ℓ') → Type (ℓ-max ℓ ℓ')
isωPropᴰ {X = X} Xᴰ = ∀ n (x : X .Xᵢ n) → isProp (Xᴰ .Xᵢᴰ n x)

mkωPropᴰ : {X : ωType ℓ}
  (Xᵢᴰ : ∀ n (x : X .Xᵢ n) → Type ℓ')
  → (∀ n x → isProp (Xᵢᴰ n x))
  → (∀ n {x} → Xᵢᴰ (suc n) x → Xᵢᴰ n (X .πᵢ n x))
  → ωTypeᴰ X ℓ'
mkωPropᴰ Xᵢᴰ _ πᵢᴰ .Xᵢᴰ = Xᵢᴰ
mkωPropᴰ Xᵢᴰ _ πᵢᴰ .πᵢᴰ = πᵢᴰ

mkωChainPropᴰ : {X : ωType ℓ} (Xᴰ : ωTypeᴰ X ℓ')
  → isωPropᴰ Xᴰ
  → (c : ωChain X)
  → (∀ i → Xᴰ .Xᵢᴰ i (c .xᵢ i))
  → ωChainᴰ Xᴰ c
mkωChainPropᴰ Xᴰ Xᴰprop c xᵢᴰ .xᵢᴰ = xᵢᴰ
mkωChainPropᴰ Xᴰ Xᴰprop c xᵢᴰ .xᵢ-natᴰ i =
  isProp→PathP (λ j → Xᴰprop i (c .xᵢ-nat i j)) _ _

mkωHomPropᴰ : {X : ωType ℓ} {Y : ωType ℓ'}
  (Xᴰ : ωTypeᴰ X ℓ'')
  (Yᴰ : ωTypeᴰ Y ℓ'')
  → isωPropᴰ Yᴰ
  → (f : ωHom X Y)
  → (∀ i {x} (xᴰ : Xᴰ .Xᵢᴰ i x) → Yᴰ .Xᵢᴰ i (f .fᵢ i x))
  → ωHomᴰ Xᴰ Yᴰ f
mkωHomPropᴰ Xᴰ Yᴰ Yᴰprop f fᵢᴰ .fᵢᴰ = fᵢᴰ
mkωHomPropᴰ Xᴰ Yᴰ Yᴰprop f fᵢᴰ .fᵢ-natᴰ n {x} xᴰ =
  isProp→PathP (λ j → Yᴰprop n (f .fᵢ-nat n x j)) _ _

isPropωChainᴰ : {X : ωType ℓ} (Xᴰ : ωTypeᴰ X ℓ') (c : ωChain X)
  → isωPropᴰ Xᴰ
  → isProp (ωChainᴰ Xᴰ c)
isPropωChainᴰ Xᴰ c Xᴰprop cᴰ dᴰ =
  makeωChainPathᴰ (λ n x → isProp→isSet (Xᴰprop n x))
    refl (funExt λ i → Xᴰprop i _ _ _)

-- Displayed ω+Typeᴰ over X: all fibers propositional
isω+Propᴰ : {X : ω+Type ℓ} (Xᴰ : ω+Typeᴰ X ℓ') → Type (ℓ-max ℓ ℓ')
isω+Propᴰ Xᴰ = isωPropᴰ (Xᴰ .Xfinᴰ)
  × (∀ x → isProp (Xᴰ .Xωᴰ x))

-- Build a displayed ω+Typeᴰ from propositional fibers
mkω+Propᴰ : {X : ω+Type ℓ}
  (Xfinᴰ : ωTypeᴰ (X .Xfin) ℓ')
  → isωPropᴰ Xfinᴰ
  → (Xωᴰ : X .Xω → Type ℓ')
  → (∀ x → isProp (Xωᴰ x))
  → (πᴰ : ∀ x → Xωᴰ x → ωChainᴰ Xfinᴰ (X .π x))
  → (limᴰ : ∀ x → ωChainᴰ Xfinᴰ (X .π x) → Xωᴰ x)
  → ω+Typeᴰ X ℓ'
mkω+Propᴰ Xfinᴰ Xfinᴰprop Xωᴰ Xωᴰprop πᴰ limᴰ .Xfinᴰ = Xfinᴰ
mkω+Propᴰ Xfinᴰ Xfinᴰprop Xωᴰ Xωᴰprop πᴰ limᴰ .Xωᴰ = Xωᴰ
mkω+Propᴰ Xfinᴰ Xfinᴰprop Xωᴰ Xωᴰprop πᴰ limᴰ .πᴰ = πᴰ
mkω+Propᴰ {X = X} Xfinᴰ Xfinᴰprop Xωᴰ Xωᴰprop πᴰ limᴰ .isLimitᴰ x = isoToIsEquiv (theIso x)
  where
  theIso : ∀ x → Iso (Xωᴰ x) (ωChainᴰ Xfinᴰ (X .π x))
  theIso x .Iso.fun = πᴰ x
  theIso x .Iso.inv = limᴰ x
  theIso x .Iso.sec c = isPropωChainᴰ Xfinᴰ (X .π x) Xfinᴰprop _ c
  theIso x .Iso.ret y = Xωᴰprop x _ y

-- Build a displayed ω+Homᴰ into a propositional codomain
mkω+HomPropᴰ : ∀ {ℓ ℓ' ℓ''} {X : ω+Type ℓ} {Y : ω+Type ℓ'}
  (Xᴰ : ω+Typeᴰ X ℓ'')
  (Yᴰ : ω+Typeᴰ Y ℓ'')
  → isω+Propᴰ Yᴰ
  → (f : ω+Hom X Y)
  → (fFinᴰ : ωHomᴰ (Xᴰ .Xfinᴰ) (Yᴰ .Xfinᴰ) (f .fFin))
  → (fωᴰ : ∀ x (xᴰ : Xᴰ .Xωᴰ x) → Yᴰ .Xωᴰ (f .fω x))
  → ω+Homᴰ Xᴰ Yᴰ f
mkω+HomPropᴰ {X = X} {Y = Y} Xᴰ Yᴰ (Yfinᴰprop , Yωᴰprop) f fFinᴰ fωᴰ .fFinᴰ = fFinᴰ
mkω+HomPropᴰ {X = X} {Y = Y} Xᴰ Yᴰ (Yfinᴰprop , Yωᴰprop) f fFinᴰ fωᴰ .fωᴰ =
  λ xᴰ → fωᴰ _ xᴰ
mkω+HomPropᴰ {X = X} {Y = Y} Xᴰ Yᴰ (Yfinᴰprop , Yωᴰprop) f fFinᴰ fωᴰ .fω-natᴰ i {x} xᴰ =
  isProp→PathP (λ j → Yfinᴰprop i (f .fω-nat i x j)) _ _
