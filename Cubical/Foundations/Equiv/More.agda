{-# OPTIONS --safe #-}
module Cubical.Foundations.Equiv.More where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Foundations.Equiv.Base public
open import Cubical.Data.Sigma.Base

private
  variable
    ℓ ℓ' ℓ''  : Level
    A B : Type ℓ
    AP BP : A → Type ℓ

isContrP : {A : Type ℓ} → (AP : A → Type ℓ') → isContr A → Type (ℓ-max ℓ ℓ')
isContrP AP isContrA =
  Σ[ xP ∈ AP (isContrA .fst) ]
  ∀ {y} yP → PathP (λ i → AP (isContrA .snd y i)) xP yP

isContrPΣ : (isContrA : isContr A) → isContrP AP isContrA → isContr (Σ A AP)
isContrPΣ isContrA isContrAP .fst = (fst isContrA) , (fst isContrAP)
isContrPΣ isContrA isContrAP .snd (y , yP) i =
  (snd isContrA y i) , (snd isContrAP yP i)

Σf : (f : A → B) (fP : ∀ x → AP x → BP (f x)) → Σ A AP → Σ B BP
Σf f fP (x , xP) = (f x) , (fP x xP)

module _ {f : A → B}
  (fP : ∀ x → AP x → BP (f x))
  where

  fiberP : ∀ y → (yP : BP y) → fiber f y → Type _
  fiberP y yP (x , fx≡y) = Σ[ xP ∈ AP x ] PathP (λ i → BP (fx≡y i)) (fP _ xP) yP

fiberPΣ : (f : A → B) (fP : ∀ x → AP x → BP (f x))
  → ∀ {y} → (fiberY : fiber f y)
  → ∀ {yP : BP y} → fiberP {A = A}{AP = AP} fP y yP fiberY
  → fiber (Σf {A = A}{AP = AP} f fP) (y , yP)
fiberPΣ f fP fiberY fiberYP .fst = (fst fiberY) , (fst fiberYP)
fiberPΣ f fP fiberY fiberYP .snd = λ i → (snd fiberY i) , (snd fiberYP i)

-- Displayed equivalence
module _ {f : A → B}
  (isEquivF : isEquiv f)
  (fP : ∀ x → AP x → BP (f x))
  where

  isEquivP : Type _
  isEquivP = ∀ {y : B}(yP : BP y)
    → isContrP (fiberP {A = A}{AP = AP} fP y yP) (isEquivF .equiv-proof y)

-- isEquivPΣ : {f : A → B}{fP : ∀ {x} → AP x → BP (f x)}
--   (isEquivF : isEquiv f)
--   → isEquivP {AP = AP}{BP = BP} isEquivF fP
--   → isEquiv {A = Σ A AP}{B = Σ B BP} λ (x , xP) → f x , fP {x} xP
-- isEquivPΣ {f = f}{fP = fP} isEquivF isEquivFP .equiv-proof (y , yP) .fst =
--   fiberPΣ f fP (isEquivF .equiv-proof y .fst) (isEquivFP yP .fst)
-- isEquivPΣ {f = f} {fP = fP} isEquivF isEquivFP .equiv-proof (y , yP) .snd y₁ = {!!}
