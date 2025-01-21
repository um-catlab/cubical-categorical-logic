module Gluing.Set where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

data Test1 : Type ℓ-zero where
  A1 : Test1

DiscreteTest1 : Discrete Test1
DiscreteTest1 A1 A1 = yes refl

isSetTest1 : isSet Test1
isSetTest1 = Discrete→isSet DiscreteTest1

data Test2 : Type ℓ-zero where
  A2 : Test2
  B2 : Test2

A2≠B2 : ¬ (A2 ≡ B2)
A2≠B2 p = subst (λ {A2 → Unit ; B2 → ⊥}) p tt

DiscreteTest2 : Discrete Test2
DiscreteTest2 A2 A2 = yes refl
DiscreteTest2 A2 B2 = no A2≠B2
DiscreteTest2 B2 A2 = no $ A2≠B2 ∘S sym
DiscreteTest2 B2 B2 = yes refl

isSetTest2 : isSet Test2
isSetTest2 = Discrete→isSet DiscreteTest2

data Test3 : Type ℓ-zero where
  A3 : Test3
  B3 : Test2 → Test3

codeTest2 : Test2 → Test2 → Type ℓ-zero
codeTest2 A2 A2 = Unit
codeTest2 A2 B2 = ⊥
codeTest2 B2 A2 = ⊥
codeTest2 B2 B2 = Unit

r2 : (x : Test2) → codeTest2 x x
r2 A2 = tt
r2 B2 = tt

encodeTest2 : (x y : Test2) → x ≡ y → codeTest2 x y
encodeTest2 A2 A2 _ = tt
encodeTest2 A2 B2 = A2≠B2
encodeTest2 B2 A2 = A2≠B2 ∘S sym
encodeTest2 B2 B2 _ = tt

A3≠B3 : ∀{x} → ¬ (A3 ≡ B3 x)
A3≠B3 p = subst {A = Test3} {x = A3} {y = B3 _} ((λ { A3 → Unit ; (B3 _) → ⊥ })) p tt

codeTest3 : Test3 → Test3 → Type ℓ-zero
codeTest3 A3 A3 = Unit
codeTest3 A3 (B3 y) = ⊥
codeTest3 (B3 x) A3 = ⊥
codeTest3 (B3 x) (B3 y) = codeTest2 x y

r3 : (x : Test3) → codeTest3 x x
r3 A3 = tt
r3 (B3 x) = r2 x

encodeTest3 : (x y : Test3) → x ≡ y → codeTest3 x y
encodeTest3 A3 A3 _ = tt
encodeTest3 A3 (B3 x) = A3≠B3
encodeTest3 (B3 x) A3 = A3≠B3 ∘S sym
encodeTest3 (B3 x) (B3 y) p = {!!}

encodeTest3' : (x y : Test3) → x ≡ y → codeTest3 x y
encodeTest3' x y p = subst (codeTest3 x) p (r3 x)

inj-B3 : ∀ x' y' → B3 x' ≡ B3 y' → x' ≡ y'
inj-B3 x' y' p = {!p!}

cong-B3-Dec : ∀ x' y' → Dec (x' ≡ y') → Dec (B3 x' ≡ B3 y')
cong-B3-Dec x' y' (yes p) = yes $ congS B3 p
cong-B3-Dec x' y' (no ¬p) = no $ ¬p ∘S (inj-B3 x' y')

DiscreteTest3 : Discrete Test3
DiscreteTest3 A3 A3 = yes refl
DiscreteTest3 A3 (B3 x) = no A3≠B3
DiscreteTest3 (B3 x) A3 = no $ A3≠B3 ∘S sym
DiscreteTest3 (B3 x) (B3 y) = cong-B3-Dec x y (DiscreteTest2 x y)

isSetTest3 : isSet Test3
isSetTest3 = Discrete→isSet DiscreteTest3

---- The "encode-decode" method from the HoTT book
--Encoding2 : Test2 → Test2 → Type ℓ-zero
--Encoding2 A2 A2 = Unit
--Encoding2 A2 B2 = ⊥
--Encoding2 B2 A2 = ⊥
--Encoding2 B2 B2 = Unit
--
--Encode2 : (x y : Test2) → x ≡ y → Encoding2 x y
--Encode2 A2 A2 p = tt
--Encode2 A2 B2 p = A2≠B2 p
--Encode2 B2 A2 p = A2≠B2 (sym p)
--Encode2 B2 B2 p = tt
--
--Decode2 : (x y : Test2) → Encoding2 x y → x ≡ y
--Decode2 A2 A2 _ = refl
--Decode2 B2 B2 _ = refl
--
--Lemma2 : (x : Test2) → (Decode2 x x) ∘S (Encode2 x x) ≡ idfun _
--Lemma2 A2 = funExt (λ p → {!!})
--Lemma2 B2 = {!!}

