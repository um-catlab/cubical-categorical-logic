module Cubical.Categories.Instances.Injections where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding
open import Cubical.Functions.Fibration

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.FinData
import Cubical.Data.FinData.FinSet as FinData
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
import Cubical.Data.SumFin.Properties as SumFin

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Categories.Category

private
  variable
    n m k : ℕ

Injection : ℕ → ℕ → Type
Injection n m = Fin n ↪ Fin m

injection≡ : {n m : ℕ} {f g : Injection n m} → f .fst ≡ g .fst → f ≡ g
injection≡ = Σ≡Prop (λ _ → isPropIsEmbedding)

isSetInjection : {n m : ℕ} → isSet (Injection n m)
isSetInjection {n} {m} =
  isSetΣSndProp
    (isSet→ {A = Fin n} (isSetFin {k = m}))
    (λ _ → isPropIsEmbedding)

idInjection : Injection n n
idInjection {n} = id↪ (Fin n)

composeInjection : {n m k : ℕ} → Injection n m → Injection m k → Injection n k
composeInjection f g = compEmbedding g f

extendInjection : {p ext : ℕ} → Injection p (p + ext)
extendInjection {p} {ext} =
  compEmbedding
    (Equiv→Embedding (FinSumChar.Equiv p ext))
    (inl , isEmbedding-inl)

ImageFiber : {n m : ℕ} → Injection n m → Fin m → Type
ImageFiber {n} {m} f y = fiber {A = Fin n} {B = Fin m} (f .fst) y

image? : {n m : ℕ} → (f : Injection n m) (y : Fin m) →
  Dec (ImageFiber {n} {m} f y)
image? {n} {m} f y =
  FinData.DecΣ n (λ x → f .fst x ≡ y)
    (λ x → discreteFin {k = m} (f .fst x) y)

Complement : {n m : ℕ} → Injection n m → Type
Complement {n} {m} f =
  Σ[ y ∈ Fin m ] ¬ ImageFiber {n} {m} f y

notInImage? : {n m : ℕ} → (f : Injection n m) (y : Fin m) →
  Dec (¬ ImageFiber {n} {m} f y)
notInImage? f y with image? f y
... | yes in-image = no (λ not-in-image → not-in-image in-image)
... | no not-in-image = yes not-in-image

complementFinOrd : {n m : ℕ} → (f : Injection n m) →
  isFinOrd (Complement f)
complementFinOrd {n} {m} f =
  isFinOrdΣ
    (Fin m)
    (m , SumFin.FinData≃SumFin)
    (λ y → ¬ ImageFiber {n} {m} f y)
    (λ y → DecProp→isFinOrd
      (((¬ ImageFiber {n} {m} f y) , isPropΠ (λ _ → isProp⊥))
      , notInImage? f y))

complementSize : {n m : ℕ} → Injection n m → ℕ
complementSize f = complementFinOrd f .fst

isFinSetComplement : {n m : ℕ} → (f : Injection n m) →
  isFinSet (Complement f)
isFinSetComplement f = isFinOrd→isFinSet (complementFinOrd f)

imageComplementIso : {n m : ℕ} → (f : Injection n m) →
  Iso (Fin n ⊎ Complement f) (Fin m)
imageComplementIso {n} {m} f = iso to from secProof retProof
  where
  to : Fin n ⊎ Complement f → Fin m
  to (inl x) = f .fst x
  to (inr (y , _)) = y

  from : Fin m → Fin n ⊎ Complement f
  from y with image? {n} {m} f y
  ... | yes (x , _) = inl x
  ... | no not-in-image = inr (y , not-in-image)

  secProof : (y : Fin m) → to (from y) ≡ y
  secProof y with image? {n} {m} f y
  ... | yes (_ , p) = p
  ... | no _ = refl

  retProof : (z : Fin n ⊎ Complement f) → from (to z) ≡ z
  retProof (inl x) with image? {n} {m} f (f .fst x)
  ... | yes (x' , p) =
    cong inl (isEmbedding→Inj (f .snd) x' x p)
  ... | no not-in-image = ⊥.rec (not-in-image (x , refl))
  retProof (inr (y , not-in-image)) with image? {n} {m} f y
  ... | yes in-image = ⊥.rec (not-in-image in-image)
  ... | no _ = cong inr
    (Σ≡Prop (λ _ → isPropΠ (λ _ → isProp⊥)) refl)

finiteImageComplementIso : {n m : ℕ} → (f : Injection n m) →
  Iso (Fin n ⊎ Fin (complementSize f)) (Fin m)
finiteImageComplementIso f =
  compIso
    (⊎Iso idIso
      (equivToIso
        (compEquiv
          SumFin.FinData≃SumFin
          (invEquiv (complementFinOrd f .snd)))))
    (imageComplementIso f)

extendAlong : {n m p : ℕ} →
  (f : Injection n m) →
  Injection n p →
  Injection m (p + complementSize f)
extendAlong {p = p} f g =
  compEmbedding
    (Equiv→Embedding (FinSumChar.Equiv p (complementSize f)))
    (compEmbedding
      (⊎Monotone↪ g (id↪ (Fin (complementSize f))))
      (Equiv→Embedding
        (isoToEquiv (invIso (finiteImageComplementIso f)))))


Inj : Category ℓ-zero ℓ-zero
Inj .Category.ob = ℕ
Inj .Category.Hom[_,_] = Injection
Inj .Category.id {x = n} = idInjection {n}
Inj .Category._⋆_ {x = n} {y = m} {z = k} = composeInjection {n} {m} {k}
Inj .Category.⋆IdL {x = n} {y = m} f = injection≡ {n} {m} refl
Inj .Category.⋆IdR {x = n} {y = m} f = injection≡ {n} {m} refl
Inj .Category.⋆Assoc {x = n} {y = m} {z = k} {w = l} f g h =
  injection≡ {n} {l} refl
Inj .Category.isSetHom {x = n} {y = m} = isSetInjection {n} {m}
