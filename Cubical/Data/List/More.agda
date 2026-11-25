module Cubical.Data.List.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.List
open import Cubical.Data.List.Dependent
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' ℓ'' : Level

open Iso

module ListPathMore {A : Type ℓ} where
  open ListPath {A = A}

  private
    encode-cons : ∀ {x xs} y ys (p : x ≡ y) (q : xs ≡ ys)
      → encode (x ∷ xs) (y ∷ ys) (λ i → p i ∷ q i) ≡ (p , encode xs ys q)
    encode-cons {x} {xs} y ys p q =
      J (λ y p → encode (x ∷ xs) (y ∷ ys) (λ i → p i ∷ q i)
                   ≡ (p , encode xs ys q))
        (J (λ ys q → encode (x ∷ xs) (x ∷ ys) (λ i → x ∷ q i)
                       ≡ (refl , encode xs ys q))
          (encodeRefl (x ∷ xs) ∙ cong pairRefl (sym (encodeRefl xs)))
          q)
        p
      where
      pairRefl : Cover xs xs → Cover (x ∷ xs) (x ∷ xs)
      pairRefl c = refl , c

  encodeDecode : ∀ xs ys (c : Cover xs ys) → encode xs ys (decode xs ys c) ≡ c
  encodeDecode [] [] c = encodeRefl []
  encodeDecode [] (_ ∷ _) (lift ())
  encodeDecode (_ ∷ _) [] (lift ())
  encodeDecode (x ∷ xs) (y ∷ ys) (p , c) =
    encode-cons y ys p (decode xs ys c) ∙ cong (p ,_) (encodeDecode xs ys c)

  ≡≅Cover : ∀ xs ys → Iso (xs ≡ ys) (Cover xs ys)
  ≡≅Cover xs ys .fun = encode xs ys
  ≡≅Cover xs ys .inv = decode xs ys
  ≡≅Cover xs ys .sec = encodeDecode xs ys
  ≡≅Cover xs ys .ret = decodeEncode xs ys

-- ListP is functorial
ListP-cong-Iso : {A : Type ℓ} {B : A → Type ℓ'} {B' : A → Type ℓ''}
  → ((a : A) → Iso (B a) (B' a))
  → ∀ as → Iso (ListP B as) (ListP B' as)
ListP-cong-Iso e as = isom as
  where
  to : ∀ as → ListP _ as → ListP _ as
  to _ [] = []
  to (a ∷ _) (y ∷ ys) = e a .fun y ∷ to _ ys
  from : ∀ as → ListP _ as → ListP _ as
  from _ [] = []
  from (a ∷ _) (y ∷ ys) = e a .inv y ∷ from _ ys
  to-from : ∀ as ys → to as (from as ys) ≡ ys
  to-from _ [] = refl
  to-from (a ∷ as) (y ∷ ys) =
    cong₂ (λ y ys → y ∷ ys) (e a .sec y) (to-from as ys)
  from-to : ∀ as ys → from as (to as ys) ≡ ys
  from-to _ [] = refl
  from-to (a ∷ as) (y ∷ ys) =
    cong₂ (λ y ys → y ∷ ys) (e a .ret y) (from-to as ys)
  isom : ∀ as → Iso (ListP _ as) (ListP _ as)
  isom as .fun = to as
  isom as .inv = from as
  isom as .sec = to-from as
  isom as .ret = from-to as

-- A fibre of map f over a list is a list of fibres of f lying over it.
module _ {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
  open ListPath {A = B}

  private
    to : ∀ as bs → Cover (map f as) bs → ListP (fiber f) bs
    to [] [] _ = []
    to [] (_ ∷ _) (lift ())
    to (_ ∷ _) [] (lift ())
    to (a ∷ as) (b ∷ bs) (p , c) = (a , p) ∷ to as bs c

    from : ∀ bs → ListP (fiber f) bs → Σ[ as ∈ List A ] Cover (map f as) bs
    from [] [] = [] , lift tt
    from (b ∷ bs) ((a , p) ∷ ys) =
      a ∷ from bs ys .fst , p , from bs ys .snd

    to-from : ∀ bs ys → to (from bs ys .fst) bs (from bs ys .snd) ≡ ys
    to-from [] [] = refl
    to-from (b ∷ bs) ((a , p) ∷ ys) = cong ((a , p) ∷_) (to-from bs ys)

    from-to : ∀ as bs c → from bs (to as bs c) ≡ (as , c)
    from-to [] [] (lift tt) = refl
    from-to [] (_ ∷ _) (lift ())
    from-to (_ ∷ _) [] (lift ())
    from-to (a ∷ as) (b ∷ bs) (p , c) i =
      a ∷ from-to as bs c i .fst , p , from-to as bs c i .snd

  fiberMapIso : ∀ bs → Iso (fiber (map f) bs) (ListP (fiber f) bs)
  fiberMapIso bs = compIso
    (Σ-cong-iso-snd λ as → ListPathMore.≡≅Cover (map f as) bs)
    isom
    where
    isom : Iso (Σ[ as ∈ List A ] Cover (map f as) bs) (ListP (fiber f) bs)
    isom .fun (as , c) = to as bs c
    isom .inv = from bs
    isom .sec = to-from bs
    isom .ret (as , c) = from-to as bs c
