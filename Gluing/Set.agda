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

decodeTest2 : (x y : Test2) → codeTest2 x y → x ≡ y
decodeTest2 A2 A2 p = refl
decodeTest2 B2 B2 p = refl

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

--encodeTest3 : (x y : Test3) → x ≡ y → codeTest3 x y
--encodeTest3 A3 A3 _ = tt
--encodeTest3 A3 (B3 x) = A3≠B3
--encodeTest3 (B3 x) A3 = A3≠B3 ∘S sym
--encodeTest3 (B3 x) (B3 y) p = {!decodeTest2!}

encodeTest3' : (x y : Test3) → x ≡ y → codeTest3 x y
encodeTest3' x y p = subst (codeTest3 x) p (r3 x)

decodeTest3' : (x y : Test3) → codeTest3 x y → x ≡ y
decodeTest3' A3 A3 p = refl
decodeTest3' (B3 x) (B3 y) p = congS B3 (decodeTest2 x y p)

inj-B3 : ∀ x' y' → B3 x' ≡ B3 y' → x' ≡ y'
inj-B3 x' y' = decodeTest2 x' y' ∘S encodeTest3' (B3 x') (B3 y')

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

data Test4 : Type ℓ-zero where
  A4 : Test4
  B4 : Test4 → Test4

A4≠B4 : ∀{x} → ¬ (A4 ≡ B4 x)
A4≠B4 p = subst (λ {A4 → Unit ; (B4 _) → ⊥}) p tt

codeTest4 : Test4 → Test4 → Type ℓ-zero
codeTest4 A4 A4 = Unit
codeTest4 (B4 x) (B4 y) = codeTest4 x y
codeTest4 _ _ = ⊥

r4 : (x : Test4) → codeTest4 x x
r4 A4 = tt
r4 (B4 x) = r4 x

encodeTest4 : (x y : Test4) → x ≡ y → codeTest4 x y
encodeTest4 x y p = subst (codeTest4 x) p (r4 x)

decodeTest4 : (x y : Test4) → codeTest4 x y → x ≡ y
decodeTest4 A4 A4 p = refl
decodeTest4 (B4 x) (B4 y) p = congS B4 $ decodeTest4 x y p

inj-B4 : ∀ x y → B4 x ≡ B4 y → x ≡ y
inj-B4 x y = decodeTest4 x y ∘S encodeTest4 (B4 x) (B4 y)

cong-B4-Dec : ∀ x y → Dec (x ≡ y) → Dec (B4 x ≡ B4 y)
cong-B4-Dec x y (yes p) = yes $ congS B4 p
cong-B4-Dec x y (no ¬p) = no $ ¬p ∘S (inj-B4 x y)

DiscreteTest4 : Discrete Test4
DiscreteTest4 A4 A4 = yes refl
DiscreteTest4 A4 (B4 y) = no A4≠B4
DiscreteTest4 (B4 x) A4 = no $ A4≠B4 ∘S sym
DiscreteTest4 (B4 x) (B4 y) = cong-B4-Dec x y $ DiscreteTest4 x y

data Test5 (P5 : Test1) : Test1 → Type ℓ-zero where
  A5 : Test5 P5 P5

data Test6 (P6 : Type1) (Q6 : Type1) : Type ℓ-zero where
  A6 : Test6 P6 Q6

test : ∀ x → Test6 x x → Type ℓ-zero
test _ A6 = {!!}

blah : ∀ x → Test5 x x → Type ℓ-zero
blah _ t = {!!}

--module _ (P5 : Test4) where
--  codingTest5 : ∀{Q5} → Test5 P5 Q5 → Test5 P5 Q5 → Type ℓ-zero
--  codingTest5 x y = Unit
--
--  r5 : ∀{Q5} → (x : Test5 P5 Q5) → codingTest5 x x
--  r5 x = tt
--
--  encodeTest5 : ∀{Q5} → (x y : Test5 P5 Q5) → x ≡ y → codingTest5 x y
--  encodeTest5 x y p = subst (codingTest5 x) p (r5 x)
--
--  decodeTest5 : ∀{Q5} x y → codingTest5 x y → x ≡ y
--  decodeTest5 x y p = {!x!}
