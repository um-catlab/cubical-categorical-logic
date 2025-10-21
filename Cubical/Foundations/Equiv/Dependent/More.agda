module Cubical.Foundations.Equiv.Dependent.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Foundations.Equiv.Dependent

private
  variable
    ℓA ℓB ℓP ℓQ : Level
    A : Type ℓA
    B : Type ℓB
    P : A → Type ℓP
    Q : B → Type ℓQ

module IsoNotation {ℓ ℓ'} {A : Type ℓ}{B : Type ℓ'} (isom : Iso A B) where
  open Iso isom public
  fun≡ : ∀ {x y} → x ≡ inv y → fun x ≡ y
  fun≡ = isoFun≡ isom

  fun-inj : ∀ {y y'} → fun y ≡ fun y' → y ≡ y'
  fun-inj = isoFunInjective isom _ _

  inv-inj : ∀ {x x'} → inv x ≡ inv x' → x ≡ x'
  inv-inj = isoInvInjective isom _ _

open Iso
open IsoOver
open isIsoOver

module _ {isom : Iso A B} {fun : mapOver (isom .fun) P Q} where
  isIsoOver→isIsoΣ :
    isIsoOver isom P Q fun
    → isIso {A = Σ A P}{B = Σ B Q} λ (a , p) → Iso.fun isom a , fun a p
  isIsoOver→isIsoΣ x .fst = λ z → inv isom (z .fst) , x .inv (z .fst) (z .snd)
  isIsoOver→isIsoΣ x .snd .fst b =
    ΣPathP ((rightInv isom (b .fst)) , (x .rightInv (b .fst) (b .snd)))
  isIsoOver→isIsoΣ x .snd .snd a =
    ΣPathP ((leftInv isom (a .fst)) , (x .leftInv (a .fst) (a .snd)))

isContrOver : (P : A → Type ℓP) → isContr A → Type _
isContrOver {A = A} P (a₀ , a₀≡) =
  Σ[ p₀ ∈ P a₀ ] (∀ {a}(p : P a) → PathP (λ i → P (a₀≡ a i)) p₀ p)

fiberOver : ∀ {f : A → B}{b} → fiber f b → (fᴰ : mapOver f P Q) (q : Q b) → Type _
fiberOver {P = P}{Q = Q} (a , fa≡b) fᴰ q =
  Σ[ p ∈ P a ] PathP (λ i → Q (fa≡b i)) (fᴰ _ p) q

isEquivᴰ : ∀ {f : A → B} → isEquiv f → (fᴰ : mapOver f P Q) → Type _
isEquivᴰ {Q = Q} fEquiv fᴰ = ∀ {b}(q : Q b) →
  isContrOver (λ fib-f-b → fiberOver fib-f-b fᴰ q) (fEquiv .equiv-proof b)

isEquiv∫ : ∀ {f : A → B} (fᴰ : mapOver f P Q) (f-eqv : isEquiv f)
  → isEquivᴰ {Q = Q} f-eqv fᴰ
  → isEquiv {A = Σ A P}{B = Σ B Q}λ (a , p) → (f a) , (fᴰ a p)
isEquiv∫ fᴰ f-eqv fᴰ-eqvᴰ .equiv-proof (b , q) .fst .fst .fst = f-eqv .equiv-proof b .fst .fst
isEquiv∫ fᴰ f-eqv fᴰ-eqvᴰ .equiv-proof (b , q) .fst .fst .snd = fᴰ-eqvᴰ q .fst .fst
isEquiv∫ fᴰ f-eqv fᴰ-eqvᴰ .equiv-proof (b , q) .fst .snd = ΣPathP ((f-eqv .equiv-proof b .fst .snd) , fᴰ-eqvᴰ q .fst .snd)
isEquiv∫ fᴰ f-eqv fᴰ-eqvᴰ .equiv-proof (b , q) .snd ((a , p) , fa≡b,fᴰp≡qᴰ) i =
  ( f-eqvb .snd (a , fa≡b) i .fst
   , fᴰ-eqvᴰ q .snd (p , (λ j → fa≡b,fᴰp≡qᴰ j .snd)) i .fst)
  , λ j →
    (f-eqvb .snd (a , fa≡b) i .snd j)
    , (fᴰ-eqvᴰ q .snd (p , (λ j → fa≡b,fᴰp≡qᴰ j .snd)) i .snd j)
  where
    fa≡b = cong fst fa≡b,fᴰp≡qᴰ
    f-eqvb = f-eqv .equiv-proof b

_≃[_]_ : (P : A → Type ℓP) → A ≃ B → (Q : B → Type ℓQ) → Type _
P ≃[ (f , ∃!f⁻b ) ] Q = Σ (mapOver f P Q) (isEquivᴰ {Q = Q} ∃!f⁻b)

invEqᴰ : ∀ {eq} → P ≃[ eq ] Q → mapOver (invEq eq) Q P
invEqᴰ eqᴰ = λ a z → eqᴰ .snd z .fst .fst

IsoOverUnit→Iso : {P : Unit → Type ℓP}{Q : Unit → Type ℓQ}{isom : Iso Unit Unit}
  → IsoOver isom P Q
  → Iso (P _) (Q _)
IsoOverUnit→Iso isomᴰ .fun = isomᴰ .fun tt
IsoOverUnit→Iso isomᴰ .inv = isomᴰ .inv tt
IsoOverUnit→Iso isomᴰ .rightInv = isomᴰ .rightInv tt
IsoOverUnit→Iso isomᴰ .leftInv = isomᴰ .leftInv tt

record IsoOver' {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ}{B : Type ℓ'}
  (isom : Iso A B)(P : A → Type ℓ'')(Q : B → Type ℓ''')
  : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ''')) where
  no-eta-equality
  constructor isoover
  field
    funᴰ : mapOver (isom .fun) P Q
    invᴰ : mapOver (isom .inv) Q P
  ∫fun : Σ A P → Σ B Q
  ∫fun = λ z → Iso.fun isom (z .fst) , funᴰ (z .fst) (z .snd)
  ∫inv : Σ B Q → Σ A P
  ∫inv = λ z → Iso.inv isom (z .fst) , invᴰ (z .fst) (z .snd)
  field
    rightInvᴰ : section ∫fun ∫inv
    leftInvᴰ  : retract ∫fun ∫inv

  asIso : Iso (Σ A P) (Σ B Q)
  asIso = iso ∫fun ∫inv rightInvᴰ leftInvᴰ

  open IsoNotation asIso public

PointwiseIso→IsoOver'Id : ∀ {ℓ ℓ'' ℓ'''}{A : Type ℓ}(P : A → Type ℓ'')(Q : A → Type ℓ''')
  → (∀ a → Iso (P a) (Q a)) → IsoOver' (idIso {A = A}) P Q
PointwiseIso→IsoOver'Id P Q isoms .IsoOver'.funᴰ = λ a → fun (isoms (fun idIso a))
PointwiseIso→IsoOver'Id P Q isoms .IsoOver'.invᴰ = λ a → inv (isoms (inv idIso a))
PointwiseIso→IsoOver'Id P Q isoms .IsoOver'.rightInvᴰ b =
  ΣPathP (refl , (rightInv (isoms (b .fst)) (b .snd)))
PointwiseIso→IsoOver'Id P Q isoms .IsoOver'.leftInvᴰ a =
  ΣPathP (refl , (leftInv (isoms (a .fst)) (a .snd)))

