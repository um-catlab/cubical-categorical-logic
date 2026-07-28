{-# OPTIONS --cubical --type-in-type --warning=noUnsupportedIndexedMatch #-}

module HyperDoc.Operational.Effects.FiniteSetReduction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
import Cubical.Foundations.Isomorphism as Iso
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.ExtensionSystem
import Cubical.Data.Empty as ⊥
open import Cubical.Data.FinData
import Cubical.Data.FinData as Fin
open import Cubical.Data.Maybe
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Bijections.Product
open import Cubical.Data.Nat.Bijections.Sum
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation
import Cubical.HITs.SetQuotients.Base as SetQuotient
import Cubical.HITs.SetQuotients.Properties as SetQuotient
import Cubical.HITs.ListedFiniteSet as LF
import Cubical.Data.DescendingList.Strict.Properties as Strict

open import HyperDoc.Algebra.Base
  using (Signature; Op; arity; FreeOn; inc; ops; trunc)
open import HyperDoc.Operational.Effects.Reduction
  using (Polynomial; Relation; ⟦_⟧; mapP)
import HyperDoc.Operational.Effects.MonadicReductionSplit as Split

data MonOp : Type where
  e ⊗ : MonOp

MonΣ : Signature
MonΣ .Op = MonOp
MonΣ .arity e = 0
MonΣ .arity ⊗ = 2

open Polynomial

------------------------------------------------------------------------
-- The list polynomial

ListP : Polynomial
ListP .Shape = ℕ
ListP .size n = n

nil : ∀ {X} → ⟦ ListP ⟧ X
nil = 0 , λ ()

singleton : ∀ {X} → X → ⟦ ListP ⟧ X
singleton x = 1 , λ _ → x

_++P_ : ∀ {X} → ⟦ ListP ⟧ X → ⟦ ListP ⟧ X → ⟦ ListP ⟧ X
(n , xs) ++P (m , ys) = n + m , xs ++Fin ys

infixr 20 _++P_

------------------------------------------------------------------------
-- Commutativity and idempotence, directly on ⟦ ListP ⟧ X

data FiniteEquation {X : Type} :
  ⟦ ListP ⟧ X → ⟦ ListP ⟧ X → Type where

  comm :
    (xs ys : ⟦ ListP ⟧ X) →
    FiniteEquation (xs ++P ys) (ys ++P xs)

  idem :
    (xs : ⟦ ListP ⟧ X) →
    FiniteEquation (xs ++P xs) xs

  congˡ :
    (xs : ⟦ ListP ⟧ X) →
    ∀ {ys zs} →
    FiniteEquation ys zs →
    FiniteEquation (xs ++P ys) (xs ++P zs)

  congʳ :
    ∀ {xs ys} →
    FiniteEquation xs ys →
    (zs : ⟦ ListP ⟧ X) →
    FiniteEquation (xs ++P zs) (ys ++P zs)

FiniteR : Relation ListP
FiniteR X xs ys =
  ∥ FiniteEquation xs ys ∥₁ ,
  squash₁

map-++Fin :
  ∀ {X Y n m}
    (f : X → Y)
    (xs : Fin n → X)
    (ys : Fin m → X) →
  (λ i → f ((xs ++Fin ys) i))
    ≡ (λ i → f (xs i)) ++Fin (λ i → f (ys i))
map-++Fin {n = 0} f xs ys = refl
map-++Fin {n = suc n} f xs ys i zero =
  f (xs zero)
map-++Fin {n = suc n} f xs ys i (suc j) =
  map-++Fin f (λ k → xs (suc k)) ys i j

map-++P :
  ∀ {X Y} (f : X → Y) (xs ys : ⟦ ListP ⟧ X) →
  mapP f (xs ++P ys) ≡ mapP f xs ++P mapP f ys
map-++P f (n , xs) (m , ys) =
  ΣPathP (refl , map-++Fin f xs ys)

map-equation :
  ∀ {X Y} (f : X → Y) {xs ys : ⟦ ListP ⟧ X} →
  FiniteEquation xs ys →
  FiniteEquation (mapP f xs) (mapP f ys)
map-equation f (comm xs ys) =
  subst2 FiniteEquation
    (sym (map-++P f xs ys))
    (sym (map-++P f ys xs))
    (comm (mapP f xs) (mapP f ys))
map-equation f (idem xs) =
  subst2 FiniteEquation
    (sym (map-++P f xs xs))
    refl
    (idem (mapP f xs))
map-equation f (congˡ xs equation) =
  subst2 FiniteEquation
    (sym (map-++P f xs _))
    (sym (map-++P f xs _))
    (congˡ (mapP f xs) (map-equation f equation))
map-equation f (congʳ equation zs) =
  subst2 FiniteEquation
    (sym (map-++P f _ zs))
    (sym (map-++P f _ zs))
    (congʳ (map-equation f equation) (mapP f zs))

FiniteR-map :
  ∀ {X Y : hSet ℓ-zero}
    (f : ⟨ X ⟩ → ⟨ Y ⟩) xs ys →
  ⟨ FiniteR X xs ys ⟩ →
  ⟨ FiniteR Y (mapP f xs) (mapP f ys) ⟩
FiniteR-map f xs ys =
  Cubical.HITs.PropositionalTruncation.map
    (map-equation f)

module FiniteReduction =
  Split.SetQuotientMonadicReduction
    MonΣ ListP FiniteR FiniteR-map

------------------------------------------------------------------------
-- The quotient

Finite : hSet ℓ-zero → hSet ℓ-zero
Finite = FiniteReduction.T

quoteT :
  ∀ {X : hSet ℓ-zero} →
  ⟦ ListP ⟧ ⟨ X ⟩ → ⟨ Finite X ⟩
quoteT = FiniteReduction.quoteT

FiniteFunctor : Functor (SET ℓ-zero) (SET ℓ-zero)
FiniteFunctor = FiniteReduction.QuotientFunctor

comm/ :
  ∀ {X : hSet ℓ-zero}
    (xs ys : ⟦ ListP ⟧ ⟨ X ⟩) →
  quoteT (xs ++P ys) ≡ quoteT (ys ++P xs)
comm/ xs ys =
  SetQuotient.eq/ _ _ ∣ comm xs ys ∣₁

idem/ :
  ∀ {X : hSet ℓ-zero}
    (xs : ⟦ ListP ⟧ ⟨ X ⟩) →
  quoteT (xs ++P xs) ≡ quoteT xs
idem/ xs =
  SetQuotient.eq/ _ _ ∣ idem xs ∣₁

------------------------------------------------------------------------
-- Semilattice structure

equation/ :
  ∀ {X : hSet ℓ-zero} {xs ys : ⟦ ListP ⟧ ⟨ X ⟩} →
  FiniteEquation xs ys → quoteT xs ≡ quoteT ys
equation/ equation =
  SetQuotient.eq/ _ _ ∣ equation ∣₁

_∪_ :
  ∀ {X : hSet ℓ-zero} →
  ⟨ Finite X ⟩ → ⟨ Finite X ⟩ → ⟨ Finite X ⟩
_∪_ {X} =
  SetQuotient.rec2
    SetQuotient.squash/
    (λ xs ys → quoteT (xs ++P ys))
    (λ xs ys zs r →
      Cubical.HITs.PropositionalTruncation.rec
        (SetQuotient.squash/ _ _)
        (λ equation → equation/ (congʳ equation zs))
        r)
    (λ xs ys zs r →
      Cubical.HITs.PropositionalTruncation.rec
        (SetQuotient.squash/ _ _)
        (λ equation → equation/ (congˡ xs equation))
        r)

infixr 20 _∪_

∅ : ∀ {X : hSet ℓ-zero} → ⟨ Finite X ⟩
∅ = quoteT nil

∪-comm :
  ∀ {X : hSet ℓ-zero} (xs ys : ⟨ Finite X ⟩) →
  xs ∪ ys ≡ ys ∪ xs
∪-comm =
  SetQuotient.elimProp2
    (λ _ _ → SetQuotient.squash/ _ _)
    comm/

∪-idem :
  ∀ {X : hSet ℓ-zero} (xs : ⟨ Finite X ⟩) →
  xs ∪ xs ≡ xs
∪-idem =
  SetQuotient.elimProp
    (λ _ → SetQuotient.squash/ _ _)
    idem/

++P-assoc :
  ∀ {X} (xs ys zs : ⟦ ListP ⟧ X) →
  xs ++P (ys ++P zs) ≡ (xs ++P ys) ++P zs
++P-assoc (n , xs) (m , ys) (k , zs) =
  ΣPathP (+-assoc n m k , ++FinAssoc xs ys zs)

++P-idr :
  ∀ {X} (xs : ⟦ ListP ⟧ X) → xs ++P nil ≡ xs
++P-idr (n , xs) =
  ΣPathP (+-zero n , ++FinRid xs (λ ()))

∪-assoc :
  ∀ {X : hSet ℓ-zero} (xs ys zs : ⟨ Finite X ⟩) →
  xs ∪ (ys ∪ zs) ≡ (xs ∪ ys) ∪ zs
∪-assoc =
  SetQuotient.elimProp
    (λ _ → isPropΠ2 λ _ _ → SetQuotient.squash/ _ _)
    λ xs →
      SetQuotient.elimProp
        (λ _ → isPropΠ λ _ → SetQuotient.squash/ _ _)
        λ ys →
          SetQuotient.elimProp
            (λ _ → SetQuotient.squash/ _ _)
            (λ zs → cong quoteT (++P-assoc xs ys zs))

∪-unitl :
  ∀ {X : hSet ℓ-zero} (xs : ⟨ Finite X ⟩) → ∅ ∪ xs ≡ xs
∪-unitl =
  SetQuotient.elimProp
    (λ _ → SetQuotient.squash/ _ _)
    (λ _ → refl)

∪-unitr :
  ∀ {X : hSet ℓ-zero} (xs : ⟨ Finite X ⟩) → xs ∪ ∅ ≡ xs
∪-unitr =
  SetQuotient.elimProp
    (λ _ → SetQuotient.squash/ _ _)
    (λ xs → cong quoteT (++P-idr xs))

------------------------------------------------------------------------
-- Finite-set bind

{-# TERMINATING #-}
fold :
  ∀ {X Y : hSet ℓ-zero} →
  (⟨ X ⟩ → ⟨ Finite Y ⟩) →
  ⟦ ListP ⟧ ⟨ X ⟩ →
  ⟨ Finite Y ⟩
fold f (0 , xs) = ∅
fold f (suc n , xs) =
  f (xs zero) ∪ fold f (n , λ i → xs (suc i))

++P-idl :
  ∀ {X} (xs : Fin 0 → X) (ys : ⟦ ListP ⟧ X) →
  (0 , xs) ++P ys ≡ ys
++P-idl xs (n , ys) = refl

fold-++ :
  ∀ {X Y : hSet ℓ-zero}
    (f : ⟨ X ⟩ → ⟨ Finite Y ⟩)
    (xs ys : ⟦ ListP ⟧ ⟨ X ⟩) →
  fold f (xs ++P ys) ≡ fold f xs ∪ fold f ys
fold-++ f (0 , xs) ys =
  cong (fold f) (++P-idl xs ys)
  ∙ sym (∪-unitl (fold f ys))
fold-++ f (suc n , xs) ys =
  cong (f (xs zero) ∪_) (fold-++ f (n , λ i → xs (suc i)) ys)
  ∙ ∪-assoc
      (f (xs zero))
      (fold f (n , λ i → xs (suc i)))
      (fold f ys)

fold-equation :
  ∀ {X Y : hSet ℓ-zero}
    (f : ⟨ X ⟩ → ⟨ Finite Y ⟩)
    {xs ys : ⟦ ListP ⟧ ⟨ X ⟩} →
  FiniteEquation xs ys → fold f xs ≡ fold f ys
fold-equation f (comm xs ys) =
  fold-++ f xs ys
  ∙ ∪-comm (fold f xs) (fold f ys)
  ∙ sym (fold-++ f ys xs)
fold-equation f (idem xs) =
  fold-++ f xs xs
  ∙ ∪-idem (fold f xs)
fold-equation f (congˡ xs equation) =
  fold-++ f xs _
  ∙ cong (fold f xs ∪_) (fold-equation f equation)
  ∙ sym (fold-++ f xs _)
fold-equation f (congʳ equation zs) =
  fold-++ f _ zs
  ∙ cong (_∪ fold f zs) (fold-equation f equation)
  ∙ sym (fold-++ f _ zs)

bindF :
  ∀ {X Y : hSet ℓ-zero} →
  (⟨ X ⟩ → ⟨ Finite Y ⟩) →
  ⟨ Finite X ⟩ →
  ⟨ Finite Y ⟩
bindF {X} {Y} f =
  SetQuotient.rec
    SetQuotient.squash/
    (fold f)
    (λ xs ys r →
      Cubical.HITs.PropositionalTruncation.rec
        (SetQuotient.squash/ _ _)
        (fold-equation f)
        r)

ηF : ∀ {X : hSet ℓ-zero} → ⟨ X ⟩ → ⟨ Finite X ⟩
ηF x = quoteT (singleton x)

bindF-η :
  ∀ {X Y : hSet ℓ-zero}
    (f : ⟨ X ⟩ → ⟨ Finite Y ⟩) x →
  bindF f (ηF x) ≡ f x
bindF-η f x = ∪-unitr (f x)

finSuc-ext :
  ∀ {X n} (f g : Fin (suc n) → X) →
  f zero ≡ g zero →
  (∀ i → f (suc i) ≡ g (suc i)) →
  f ≡ g
finSuc-ext {n = n} f g p₀ ps =
  funExt λ i →
    sym (cong f (Iso.Iso.ret finSucMaybeIso i))
    ∙ cases (Iso.Iso.fun finSucMaybeIso i)
    ∙ cong g (Iso.Iso.ret finSucMaybeIso i)
  where
  cases :
    (m : Maybe (Fin n)) →
    f (Iso.Iso.inv finSucMaybeIso m) ≡
    g (Iso.Iso.inv finSucMaybeIso m)
  cases nothing = p₀
  cases (just i) = ps i

consP :
  ∀ {X n} (xs : Fin (suc n) → X) →
  singleton (xs zero) ++P (n , λ i → xs (suc i)) ≡ (suc n , xs)
consP xs =
  ΣPathP
    ( refl
    , finSuc-ext _ xs refl (λ _ → refl)
    )

emptyP :
  ∀ {X} (xs : Fin 0 → X) → (0 , xs) ≡ nil
emptyP xs =
  ΣPathP (refl , funExt λ i → ⊥.rec (¬Fin0 i))

bindF-unit :
  ∀ {X : hSet ℓ-zero} (xs : ⟨ Finite X ⟩) →
  bindF ηF xs ≡ xs
bindF-unit =
  SetQuotient.elimProp
    (λ _ → SetQuotient.squash/ _ _)
    representative
  where
  representative :
    ∀ {X : hSet ℓ-zero} (xs : ⟦ ListP ⟧ ⟨ X ⟩) →
    fold ηF xs ≡ quoteT xs
  representative (0 , xs) =
    cong quoteT (sym (emptyP xs))
  representative (suc n , xs) =
    cong (ηF (xs zero) ∪_)
      (representative (n , λ i → xs (suc i)))
    ∙ cong quoteT (consP xs)

bindF-∪ :
  ∀ {X Y : hSet ℓ-zero}
    (f : ⟨ X ⟩ → ⟨ Finite Y ⟩)
    (xs ys : ⟨ Finite X ⟩) →
  bindF f (xs ∪ ys) ≡ bindF f xs ∪ bindF f ys
bindF-∪ f =
  SetQuotient.elimProp
    (λ _ → isPropΠ λ _ → SetQuotient.squash/ _ _)
    λ xs →
      SetQuotient.elimProp
        (λ _ → SetQuotient.squash/ _ _)
        (λ ys → fold-++ f xs ys)

bindF-assoc :
  ∀ {X Y Z : hSet ℓ-zero}
    (f : ⟨ X ⟩ → ⟨ Finite Y ⟩)
    (g : ⟨ Y ⟩ → ⟨ Finite Z ⟩)
    (xs : ⟨ Finite X ⟩) →
  bindF g (bindF f xs)
    ≡ bindF (λ x → bindF g (f x)) xs
bindF-assoc {X} {Y} {Z} f g =
  SetQuotient.elimProp
    (λ _ → SetQuotient.squash/ _ _)
    representative
  where
  representative :
    (xs : ⟦ ListP ⟧ ⟨ X ⟩) →
    bindF g (fold f xs)
      ≡ fold (λ x → bindF g (f x)) xs
  representative (0 , xs) = refl
  representative (suc n , xs) =
    bindF-∪ g (f (xs zero)) (fold f (n , λ i → xs (suc i)))
    ∙ cong (bindF g (f (xs zero)) ∪_)
        (representative (n , λ i → xs (suc i)))

FiniteMonad : ExtensionSystemFor (SET ℓ-zero) Finite
FiniteMonad .ExtensionSystemFor.η = ηF
FiniteMonad .ExtensionSystemFor.bind = bindF
FiniteMonad .ExtensionSystemFor.bind-r =
  funExt bindF-unit
FiniteMonad .ExtensionSystemFor.bind-l =
  funExt λ x → bindF-η _ x
FiniteMonad .ExtensionSystemFor.bind-comp =
  funExt λ xs → bindF-assoc _ _ xs

------------------------------------------------------------------------
-- Monoid algebra and monadic reduction, stopping before Terms

Finite-alg :
  (X : hSet ℓ-zero) →
  HyperDoc.Algebra.Base.IsAlg MonΣ (Finite X)
Finite-alg X e args = ∅
Finite-alg X ⊗ args =
  args zero ∪ args (suc zero)

quoteT-resp :
  ∀ X xs ys →
  ⟨ FiniteR X xs ys ⟩ →
  quoteT {X = X} xs ≡ quoteT ys
quoteT-resp X xs ys r =
  SetQuotient.eq/ xs ys r

module FiniteMonadicReduction =
  Split.MonadicReductionSplit
    MonΣ
    ListP
    FiniteR
    Finite
    (λ X → quoteT {X = X})
    quoteT-resp
    FiniteMonad
    Finite-alg

------------------------------------------------------------------------
module ChoiceOrder
  (X : Type)
  (encodeX : X → ℕ)
  (decodeX : ℕ → X)
  (decode-encodeX : (x : X) → decodeX (encodeX x) ≡ x)
  where

  TermX : Type
  TermX = FreeOn MonΣ X

  private
    Tag : Type
    Tag = ℕ ⊎ (ℕ ⊎ ℕ)

    tag : Tag → ℕ
    tag (inl n) = Iso.Iso.fun ℕ⊎ℕ≅ℕ (inl n)
    tag (inr s) =
      Iso.Iso.fun ℕ⊎ℕ≅ℕ
        (inr (Iso.Iso.fun ℕ⊎ℕ≅ℕ s))

    untag-sum : ℕ ⊎ ℕ → Tag
    untag-sum (inl k) = inl k
    untag-sum (inr k) =
      inr (Iso.Iso.inv ℕ⊎ℕ≅ℕ k)

    untag : ℕ → Tag
    untag n =
      untag-sum (Iso.Iso.inv ℕ⊎ℕ≅ℕ n)

    untag-tag : (s : Tag) → untag (tag s) ≡ s
    untag-tag (inl n) =
      cong untag-sum
        (Iso.Iso.ret ℕ⊎ℕ≅ℕ (inl n))
    untag-tag (inr s) =
      cong untag-sum
        (Iso.Iso.ret ℕ⊎ℕ≅ℕ
          (inr (Iso.Iso.fun ℕ⊎ℕ≅ℕ s)))
      ∙ cong inr (Iso.Iso.ret ℕ⊎ℕ≅ℕ s)

    pair : ℕ → ℕ → ℕ
    pair m n =
      Iso.Iso.fun ℕ×ℕ≅ℕ (m , n)

    unpair : ℕ → ℕ × ℕ
    unpair = Iso.Iso.inv ℕ×ℕ≅ℕ

  encode : TermX → ℕ
  encode (inc x) = tag (inl (encodeX x))
  encode (ops e args) = tag (inr (inl 0))
  encode (ops ⊗ args) =
    tag (inr (inr
      (pair (encode (args zero))
            (encode (args (suc zero))))))
  encode (trunc x y p q i j) =
    isSetℕ
      (encode x) (encode y)
      (cong encode p) (cong encode q) i j

  {-# TERMINATING #-}
  mutual
    decode : ℕ → TermX
    decode n = decode-tag (untag n)

    decode-tag : Tag → TermX
    decode-tag (inl k) = inc (decodeX k)
    decode-tag (inr (inl _)) = ops e λ ()
    decode-tag (inr (inr k)) =
      ops ⊗
        (Fin.rec
          (decode (fst (unpair k)))
          (decode (snd (unpair k))))

  fin2-path :
    ∀ {A : Type} (f g : Fin 2 → A) →
    f zero ≡ g zero →
    f (suc zero) ≡ g (suc zero) →
    f ≡ g
  fin2-path f g p₀ p₁ =
    funExt λ i →
      sym (cong f (Iso.Iso.ret finSucMaybeIso i))
      ∙ cases (Iso.Iso.fun finSucMaybeIso i)
      ∙ cong g (Iso.Iso.ret finSucMaybeIso i)
    where
    cases :
      (m : Maybe (Fin 1)) →
      f (Iso.Iso.inv finSucMaybeIso m) ≡
      g (Iso.Iso.inv finSucMaybeIso m)
    cases nothing = p₀
    cases (just j) =
      sym
        (cong (λ k → f (suc k))
          (isContrFin1 .snd j))
      ∙ p₁
      ∙ cong (λ k → g (suc k))
          (isContrFin1 .snd j)

  decode-encode : (t : TermX) → decode (encode t) ≡ t
  decode-encode (inc x) =
    cong decode-tag (untag-tag (inl (encodeX x)))
    ∙ cong inc (decode-encodeX x)
  decode-encode (ops e args) =
    cong decode-tag (untag-tag (inr (inl 0)))
    ∙ cong (ops e)
        (funExt λ i → ⊥.rec (¬Fin0 i))
  decode-encode (ops ⊗ args) =
    cong decode-tag
      (untag-tag
        (inr (inr
          (pair (encode (args zero))
                (encode (args (suc zero)))))))
    ∙ cong (ops ⊗)
        (cong
          (λ p →
            Fin.rec
              (decode (fst p))
              (decode (snd p)))
          (Iso.Iso.ret ℕ×ℕ≅ℕ
            (encode (args zero) ,
             encode (args (suc zero)))))
    ∙ cong (ops ⊗)
        (fin2-path
          (Fin.rec
            (decode (encode (args zero)))
            (decode (encode (args (suc zero)))))
          args
          (decode-encode (args zero))
          (decode-encode (args (suc zero))))
  decode-encode (trunc x y p q i j) =
    isProp→PathP
      (λ j → trunc _ _)
      (decode-encode (p i))
      (decode-encode (q i))
      j

  encode-injective :
    ∀ {x y : TermX} →
    encode x ≡ encode y → x ≡ y
  encode-injective {x} {y} p =
    sym (decode-encode x)
    ∙ cong decode p
    ∙ decode-encode y

  discreteTerm : Discrete TermX
  discreteTerm x y
    with discreteℕ (encode x) (encode y)
  ... | yes p = yes (encode-injective p)
  ... | no ¬p =
    no (λ p → ¬p (cong encode p))

  _>Term_ : TermX → TermX → Type
  x >Term y = encode y < encode x

  >Term-isProp : ∀ {x y} → isProp (x >Term y)
  >Term-isProp {x} {y} = Cubical.Data.Nat.Order.isProp≤

  term-tri :
    ∀ x y →
    Strict.Tri TermX _>Term_
      (y >Term x) (x ≡ y) (x >Term y)
  term-tri x y with Cubical.Data.Nat.Order._≟_ (encode x) (encode y)
  ... | Trichotomy.lt p =
    Strict.tri-<
      p
      (λ q →
        ¬m<m
          (subst (encode x <_)
            (sym (cong encode q)) p))
      (λ q → ¬m<m (<-trans p q))
  ... | Trichotomy.eq p =
    Strict.tri-≡
      (λ q →
        ¬m<m (subst (_< encode y) p q))
      (encode-injective p)
      (λ q →
        ¬m<m (subst (encode y <_) p q))
  ... | Trichotomy.gt p =
    Strict.tri->
      (λ q → ¬m<m (<-trans q p))
      (λ q →
        ¬m<m
          (subst (encode y <_)
            (cong encode q) p))
      p

  >Term-trans :
    ∀ {x y z} →
    x >Term y → y >Term z → x >Term z
  >Term-trans {x} {y} {z} x>y y>z =
    <-trans y>z x>y

  >Term-irrefl : ∀ {x} → ¬ x >Term x
  >Term-irrefl {x} = ¬m<m

-- Choice at X = Term Bool

TermBool : Type
TermBool = FreeOn MonΣ Bool

X : hSet ℓ-zero
X = TermBool , trunc

encodeBool : Bool → ℕ
encodeBool false = 0
encodeBool true = 1

decodeBool : ℕ → Bool
decodeBool 0 = false
decodeBool (suc _) = true

decode-encodeBool :
  (x : Bool) → decodeBool (encodeBool x) ≡ x
decode-encodeBool false = refl
decode-encodeBool true = refl

module Order =
  ChoiceOrder Bool encodeBool decodeBool decode-encodeBool

{-# TERMINATING #-}
toLF : ⟦ ListP ⟧ TermBool → LF.LFSet TermBool
toLF (0 , xs) = LF.[]
toLF (suc n , xs) =
  xs zero LF.∷ toLF (n , λ i → xs (suc i))

toLF-++ :
  (xs ys : ⟦ ListP ⟧ TermBool) →
  toLF (xs ++P ys) ≡ toLF xs LF.++ toLF ys
toLF-++ (0 , xs) (m , ys) = refl
toLF-++ (suc n , xs) ys =
  cong (xs zero LF.∷_)
    (toLF-++ (n , λ i → xs (suc i)) ys)

toLF-equation :
  ∀ {xs ys : ⟦ ListP ⟧ TermBool} →
  FiniteEquation xs ys → toLF xs ≡ toLF ys
toLF-equation (comm xs ys) =
  toLF-++ xs ys
  ∙ LF.comm-++ (toLF xs) (toLF ys)
  ∙ sym (toLF-++ ys xs)
toLF-equation (idem xs) =
  toLF-++ xs xs
  ∙ LF.idem-++ (toLF xs)
toLF-equation (congˡ xs equation) =
  toLF-++ xs _
  ∙ cong (toLF xs LF.++_) (toLF-equation equation)
  ∙ sym (toLF-++ xs _)
toLF-equation (congʳ equation zs) =
  toLF-++ _ zs
  ∙ cong (LF._++ toLF zs) (toLF-equation equation)
  ∙ sym (toLF-++ _ zs)

toLFQ : ⟨ Finite X ⟩ → LF.LFSet TermBool
toLFQ =
  SetQuotient.rec
    LF.trunc
    toLF
    (λ xs ys r →
      Cubical.HITs.PropositionalTruncation.rec
        (LF.trunc _ _)
        toLF-equation
        r)

fromLF : LF.LFSet TermBool → ⟨ Finite X ⟩
fromLF =
  LF.Rec.f
    ∅
    (λ x xs → ηF x ∪ xs)
    (λ x y xs →
      ∪-assoc (ηF x) (ηF y) xs
      ∙ cong (_∪ xs) (∪-comm (ηF x) (ηF y))
      ∙ sym (∪-assoc (ηF y) (ηF x) xs))
    (λ x xs →
      ∪-assoc (ηF x) (ηF x) xs
      ∙ cong (_∪ xs) (∪-idem (ηF x)))
    SetQuotient.squash/

from-toLFQ :
  (xs : ⟨ Finite X ⟩) →
  fromLF (toLFQ xs) ≡ xs
from-toLFQ =
  SetQuotient.elimProp
    (λ _ → SetQuotient.squash/ _ _)
    representative
  where
  representative :
    (xs : ⟦ ListP ⟧ TermBool) →
    fromLF (toLF xs) ≡ quoteT xs
  representative (0 , xs) =
    cong quoteT (sym (emptyP xs))
  representative (suc n , xs) =
    cong (ηF (xs zero) ∪_)
      (representative (n , λ i → xs (suc i)))
    ∙ cong quoteT (consP xs)

module Choice where

  open Order

  import Cubical.Data.DescendingList.Strict
    TermBool _>Term_ as Sorted
  import Cubical.Data.DescendingList.Strict.Properties
    TermBool _>Term_ as SortedProperties

  module Sort = SortedProperties.IsoToLFSet
    discreteTerm
    (λ {x} {y} → >Term-isProp {x} {y})
    term-tri
    (λ {x} {y} {z} → >Term-trans {x} {y} {z})
    (λ {x} → >Term-irrefl {x})

  forget : Sorted.SDL → ⟦ ListP ⟧ TermBool
  forget Sorted.[] = nil
  forget (Sorted.cons x xs _) =
    singleton x ++P forget xs

  quote-forget :
    (xs : Sorted.SDL) →
    quoteT (forget xs)
      ≡ fromLF (SortedProperties.unsort xs)
  quote-forget Sorted.[] = refl
  quote-forget (Sorted.cons x xs _) =
    cong (ηF x ∪_) (quote-forget xs)

  choice :
    ⟨ Finite X ⟩ → ⟦ ListP ⟧ TermBool
  choice xs =
    forget (Sort.sort (toLFQ xs))

  quote-choice :
    (u : ⟨ Finite X ⟩) →
    quoteT {X = X} (choice u) ≡ u
  quote-choice u =
    quote-forget (Sort.sort (toLFQ u))
    ∙ cong fromLF (Sort.unsort∘sort (toLFQ u))
    ∙ from-toLFQ u

open Choice using (choice; quote-choice)

module Terms =
  FiniteMonadicReduction.Terms
    (Bool , isSetBool)
    choice
    quote-choice
