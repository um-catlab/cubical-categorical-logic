{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Direct.Examples.GCD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Nat.Mod using (_mod_ ; mod<)
open import Cubical.Data.Nat.GCD using (isGCD ; GCD ; isPropGCD ; zeroGCD ; stepGCD)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder ; <→Wo<)
open import Cubical.Categories.Enriched.Enrichment.Instances.Power using (Setᴬ)
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive
  using (module Hylo ; isLocallyContractive)
open import Cubical.Categories.Displayed.Instances.FunctorAlgebras using (InitialAlgebra)
open import Cubical.Categories.Displayed.Instances.FunctorCoalgebras using (TerminalCoalgebra)

open Functor

Wo : WFOrder ℓ-zero ℓ-zero
Wo = pullbackWFOrder ℕWFOrder (isSet× isSetℕ isSetℕ) snd

ℕ² : Category ℓ-zero ℓ-zero
ℕ² = WFOrder→Cat Wo

dir : DirectStr ℕ² Wo
dir = Id

open DirectNotation dir using (_≺_)
open import Cubical.Categories.Direct.Guarded.Presheaf dir using (pshGuarded)
open import Cubical.Categories.Direct.Guarded.Family dir using (ΣFam ; LC-Σ ; Reindex↡ ; Reindex↡-LC)
open import Cubical.Categories.Direct.StrictDownset dir using (↡Psh)
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive.Bifunctor pshGuarded
  using (LC-const)
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Enriched.Enrichment.Instances.Family.Limits ℕ² ℓ-zero
  using (famEnrichment)
open import Cubical.Categories.Direct.ContractiveCompleteness.Family dir
  using (famInitialAlgebra ; famTerminalCoalgebra)

Fam : Category _ _
Fam = Setᴬ (ℕ × ℕ) ℓ-zero

Zero Succ : Category.ob Fam
Zero (m , n) = (n ≡ 0) , isProp→isSet (isSetℕ n 0)
Succ (m , n) = (Σ[ n₀ ∈ ℕ ] n ≡ suc n₀) , isSetΣ isSetℕ λ n₀ → isProp→isSet (isSetℕ n (suc n₀))

step : ∀ x → ⟨ Succ x ⟩ → Σ[ y ∈ ℕ × ℕ ] ⟨ ↡Psh x .F-ob y ⟩
step (m , n) (n₀ , p) = (suc n₀ , m mod suc n₀) , inl lt , lt
  where
  lt : (suc n₀ , m mod suc n₀) ≺ (m , n)
  lt = subst (λ z → (suc n₀ , m mod suc n₀) ≺ (m , z)) (sym p) (<→Wo< (mod< n₀ m))

Branch : Bool → Functor Fam Fam
Branch false = Constant Fam Fam Zero
Branch true  = Reindex↡ Succ step

H : Functor Fam Fam
H = ΣFam (Bool , isSetBool) Branch

H-LC : isLocallyContractive pshGuarded famEnrichment famEnrichment H
H-LC = LC-Σ (Bool , isSetBool) Branch λ
  { false → LC-const famEnrichment famEnrichment Zero
  ; true  → Reindex↡-LC Succ step }

Inp Out : Category.ob Fam
Inp _ = Unit , isSetUnit
Out (m , n) = GCD m n , isProp→isSet isPropGCD

coalg : Fam [ Inp , H ⟅ Inp ⟆ ]
coalg (m , zero)   tt = false , refl
coalg (m , suc n₀) tt = true , (n₀ , refl) , tt

alg : Fam [ H ⟅ Out ⟆ , Out ]
alg (m , n) (false , n≡0) =
  m , subst (λ z → isGCD m z m) (sym n≡0) (zeroGCD m)
alg (m , n) (true , (n₀ , n≡sn₀) , (d , dGCD)) =
  d , subst (λ z → isGCD m z d) (sym n≡sn₀) (stepGCD dGCD)

μH : InitialAlgebra H
μH = famInitialAlgebra H H-LC

νH : TerminalCoalgebra H
νH = famTerminalCoalgebra H H-LC

private
  module HY = Hylo pshGuarded {F = H} H-LC {X = Inp} {B = Out} coalg alg

gcdGCD : ∀ m n → GCD m n
gcdGCD m n = HY.hylo (m , n) tt

gcd : ℕ → ℕ → ℕ
gcd m n = gcdGCD m n .fst

gcd-suc : ∀ m n₀ → gcd m (suc n₀) ≡ gcd (suc n₀) (m mod suc n₀)
gcd-suc m n₀ = λ i → HY.hylo-eq i (m , suc n₀) tt .fst

_ : gcd 12 8 ≡ 4
_ = refl

_ : gcd 48 36 ≡ 12
_ = refl

_ : gcd 96 15 ≡ 3
_ = refl
