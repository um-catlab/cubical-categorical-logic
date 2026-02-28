{-

  Propositional ω-types and ω+-types.

  When each Xᵢ is a proposition, the restriction naturality
  equations come for free, simplifying the construction of
  ωTypes, ωChains, ωHoms, ω+Types and ω+Homs.

-}
module Cubical.Data.StepIndexedSet.Propositions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.StepIndexedSet.Base

open ωType
open ωHom
open ωChain
open ω+Type
open ω+Hom

private
  variable
    ℓ ℓ' : Level

isωProp : ωType ℓ → Type ℓ
isωProp X = ∀ i → isProp (X .Xᵢ i)

-- Build an ωType from propositions: naturality is automatic.
mkωProp : (Xᵢ : ℕ → Type ℓ)
  → (∀ i → isProp (Xᵢ i))
  → (∀ n → Xᵢ (suc n) → Xᵢ n)
  → ωType ℓ
mkωProp Xᵢ _ πᵢ .ωType.Xᵢ = Xᵢ
mkωProp Xᵢ _ πᵢ .ωType.πᵢ = πᵢ

-- Build an ωChain into a propositional ωType: naturality
-- is automatic.
mkωChainProp : (X : ωType ℓ) → isωProp X
  → (∀ i → X .Xᵢ i) → ωChain X
mkωChainProp X Xprop xᵢ .ωChain.xᵢ = xᵢ
mkωChainProp X Xprop xᵢ .ωChain.xᵢ-nat i =
  Xprop i _ _

-- Build an ωHom into a propositional codomain: naturality
-- is automatic.
mkωHomProp : {X : ωType ℓ} {Y : ωType ℓ'}
  → isωProp Y
  → (∀ i → X .Xᵢ i → Y .Xᵢ i) → ωHom X Y
mkωHomProp Yprop fᵢ .ωHom.fᵢ = fᵢ
mkωHomProp Yprop fᵢ .ωHom.fᵢ-nat n x = Yprop n _ _

-- Propositional ωChains are propositional.
isPropωChain : (X : ωType ℓ) → isωProp X
  → isProp (ωChain X)
isPropωChain X Xprop c d i .ωChain.xᵢ n =
  Xprop n (c .xᵢ n) (d .xᵢ n) i
isPropωChain X Xprop c d i .ωChain.xᵢ-nat n =
  isProp→PathP
    {B = λ j → X .πᵢ n
      (Xprop (suc n) (c .xᵢ (suc n))
        (d .xᵢ (suc n)) j)
      ≡ Xprop n (c .xᵢ n) (d .xᵢ n) j}
    (λ _ → isProp→isSet (Xprop n) _ _)
    (c .xᵢ-nat n) (d .xᵢ-nat n) i

-- Build an ω+Type from propositions: the limit condition
-- is automatic when Xω is also a proposition.
mkω+Prop : (Xᵢ : ℕ → Type ℓ)
  → (∀ i → isProp (Xᵢ i))
  → (πᵢ : ∀ n → Xᵢ (suc n) → Xᵢ n)
  → (Xω : Type ℓ)
  → isProp Xω
  → (π : Xω → ∀ i → Xᵢ i)
  → (lim : (∀ i → Xᵢ i) → Xω)
  → ω+Type ℓ
mkω+Prop Xᵢ Xprop πᵢ Xω Xωprop π lim .ω+Type.Xfin =
  mkωProp Xᵢ Xprop πᵢ
mkω+Prop Xᵢ Xprop πᵢ Xω Xωprop π lim .ω+Type.Xω = Xω
mkω+Prop Xᵢ Xprop πᵢ Xω Xωprop π lim .ω+Type.π x =
  mkωChainProp (mkωProp Xᵢ Xprop πᵢ) Xprop (π x)
mkω+Prop Xᵢ Xprop πᵢ Xω Xωprop π lim .isLimit =
  isoToIsEquiv theIso
  where
  theFin = mkωProp Xᵢ Xprop πᵢ
  theIso : Iso Xω (ωChain theFin)
  theIso .Iso.fun x =
    mkωChainProp theFin Xprop (π x)
  theIso .Iso.inv c = lim (c .xᵢ)
  theIso .Iso.sec c =
    isPropωChain theFin Xprop _ c
  theIso .Iso.ret x = Xωprop _ x

-- Build an ω+Hom into a propositional codomain:
-- naturality is automatic.
mkω+HomProp : {X : ω+Type ℓ} {Y : ω+Type ℓ'}
  → isωProp (Y .ω+Type.Xfin)
  → isProp (Y .ω+Type.Xω)
  → (∀ i → X .Xᵢ i → Y .Xᵢ i)
  → (X .ω+Type.Xω → Y .ω+Type.Xω)
  → ω+Hom X Y
mkω+HomProp Yprop Yωprop fᵢ fω .fFin =
  mkωHomProp Yprop fᵢ
mkω+HomProp Yprop Yωprop fᵢ fω .ω+Hom.fω = fω
mkω+HomProp Yprop Yωprop fᵢ fω .fω-nat i x =
  Yprop i _ _
