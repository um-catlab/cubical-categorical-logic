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

imageComplementIso-image : {n m : ℕ} (f : Injection n m)
  {y : Fin m} (xy : ImageFiber f y) →
  Iso.inv (imageComplementIso f) y ≡ inl (xy .fst)
imageComplementIso-image f {y} (x , fx≡y) with image? f y
... | yes (x' , fx'≡y) = cong inl
  (isEmbedding→Inj (f .snd) x' x (fx'≡y ∙ sym fx≡y))
... | no not-image = ⊥.rec (not-image (x , fx≡y))

imageComplementIso-complement : {n m : ℕ} (f : Injection n m)
  (y : Fin m) (not-image : ¬ ImageFiber f y) →
  Iso.inv (imageComplementIso f) y ≡ inr (y , not-image)
imageComplementIso-complement f y not-image with image? f y
... | yes in-image = ⊥.rec (not-image in-image)
... | no _ = cong inr
  (Σ≡Prop (λ _ → isPropΠ (λ _ → isProp⊥)) refl)

complementEnumerationIso : {n m : ℕ} (f : Injection n m) →
  Iso (Complement f) (Fin (complementSize f))
complementEnumerationIso f = equivToIso
  (complementFinOrd f .snd ∙ₑ invEquiv SumFin.FinData≃SumFin)

complementIndex : {n m : ℕ} (f : Injection n m) →
  Complement f → Fin (complementSize f)
complementIndex f = Iso.fun (complementEnumerationIso f)

finiteImageComplementIso : {n m : ℕ} → (f : Injection n m) →
  Iso (Fin n ⊎ Fin (complementSize f)) (Fin m)
finiteImageComplementIso f =
  compIso
    (⊎Iso idIso (invIso (complementEnumerationIso f)))
    (imageComplementIso f)

finiteImageComplementIso-inv : {n m : ℕ} (f : Injection n m)
  (y : Fin m) →
  Iso.inv (finiteImageComplementIso f) y
  ≡ Iso.fun (⊎Iso idIso (complementEnumerationIso f))
      (Iso.inv (imageComplementIso f) y)
finiteImageComplementIso-inv f y = inverse-sum
  (Iso.inv (imageComplementIso f) y)
  where
  inverse-sum : (s : Fin _ ⊎ Complement f) →
    Iso.inv (⊎Iso idIso (invIso (complementEnumerationIso f))) s
    ≡ Iso.fun (⊎Iso idIso (complementEnumerationIso f)) s
  inverse-sum (inl _) = refl
  inverse-sum (inr _) = refl

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

extendAlong-commutes : {n m p : ℕ}
  (f : Injection n m) (g : Injection n p) →
  composeInjection f (extendAlong f g)
  ≡ composeInjection g extendInjection
extendAlong-commutes {p = p} f g = injection≡ (funExt lemma)
  where
  ext = complementSize f

  lemma : ∀ x →
    extendAlong f g .fst (f .fst x)
    ≡ extendInjection {p} {ext} .fst (g .fst x)
  lemma x with image? f (f .fst x)
  ... | yes (x' , fx'≡fx) = cong (FinSumChar.fun p ext ∘ inl ∘ g .fst)
    (isEmbedding→Inj (f .snd) x' x fx'≡fx)
  ... | no not-in-image = ⊥.rec (not-in-image (x , refl))

extendRight : {p q : ℕ} →
  Injection p q →
  (ext : ℕ) →
  Injection (p + ext) (q + ext)
extendRight {p} {q} h ext =
  compEmbedding
    (Equiv→Embedding (FinSumChar.Equiv q ext))
    (compEmbedding
      (⊎Monotone↪ h (id↪ (Fin ext)))
      (Equiv→Embedding (invEquiv (FinSumChar.Equiv p ext))))

extendRight-map : {p q : ℕ} (h : Injection p q) (ext : ℕ)
  (z : Fin p ⊎ Fin ext) →
  extendRight h ext .fst (FinSumChar.fun p ext z)
  ≡ FinSumChar.fun q ext (Sum.map (h .fst) (idfun (Fin ext)) z)
extendRight-map {p} {q} h ext z =
  cong
    (FinSumChar.fun q ext ∘ Sum.map (h .fst) (idfun (Fin ext)))
    (FinSumChar.ret p ext z)

extendRight-extendInjection : {p q ext : ℕ} (h : Injection p q) →
  composeInjection (extendInjection {p} {ext}) (extendRight h ext)
  ≡ composeInjection h (extendInjection {q} {ext})
extendRight-extendInjection {p} {q} {ext} h = injection≡ (funExt λ x →
  cong
    (FinSumChar.fun q ext ∘ Sum.map (h .fst) (idfun (Fin ext)))
    (FinSumChar.ret p ext (inl x)))

extendAlong-natural : {n m p q : ℕ}
  (f : Injection n m) (g : Injection n p) (h : Injection p q) →
  composeInjection (extendAlong f g) (extendRight h (complementSize f))
  ≡ extendAlong f (composeInjection g h)
extendAlong-natural {p = p} {q = q} f g h = injection≡ (funExt lemma)
  where
  ext = complementSize f

  lemma : (y : Fin _) →
    extendRight h ext .fst (extendAlong f g .fst y)
    ≡ extendAlong f (composeInjection g h) .fst y
  lemma y =
    extendRight-map h ext
      (Sum.map (g .fst) (idfun (Fin ext))
        (Iso.inv (finiteImageComplementIso f) y))
    ∙ cong (FinSumChar.fun q ext)
        (map-compose (Iso.inv (finiteImageComplementIso f) y))
    where
    map-compose : (z : Fin _ ⊎ Fin ext) →
      Sum.map (h .fst) (idfun (Fin ext))
        (Sum.map (g .fst) (idfun (Fin ext)) z)
      ≡ Sum.map (composeInjection g h .fst) (idfun (Fin ext)) z
    map-compose (inl _) = refl
    map-compose (inr _) = refl

-- The canonical complement square determined by an injection.
module Extension {n m : ℕ} (f : Injection n m) where

  size : ℕ
  size = complementSize f

  decomposition : Iso (Fin n ⊎ Fin size) (Fin m)
  decomposition = finiteImageComplementIso f

  along : {p : ℕ} → Injection n p → Injection m (p + size)
  along = extendAlong f

  square : {p : ℕ} (g : Injection n p) →
    composeInjection f (along g)
    ≡ composeInjection g extendInjection
  square = extendAlong-commutes f

  right : {p q : ℕ} → Injection p q → Injection (p + size) (q + size)
  right h = extendRight h size

  right-extend : {p q : ℕ} (h : Injection p q) →
    composeInjection (extendInjection {p} {size}) (right h)
    ≡ composeInjection h (extendInjection {q} {size})
  right-extend = extendRight-extendInjection

  along-natural : {p q : ℕ}
    (g : Injection n p) (h : Injection p q) →
    composeInjection (along g) (right h)
    ≡ along (composeInjection g h)
  along-natural = extendAlong-natural f


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
