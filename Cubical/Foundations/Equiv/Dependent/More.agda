module Cubical.Foundations.Equiv.Dependent.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Dependent

private
  variable
    ℓA ℓB ℓP ℓQ : Level
    A : Type ℓA
    B : Type ℓB
    P : A → Type ℓP
    Q : B → Type ℓQ
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

module _ (isom : Iso A B) (isomᴰ : IsoOver isom P Q) where
  IsoOver→Iso : Iso (Σ A P) (Σ B Q)
  IsoOver→Iso = isIsoToIso (isIsoOver→isIsoΣ (IsoOver→isIsoOver isomᴰ))

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

module _ {isom : Iso A B} (f : mapOver (isom .fun) P Q) (f⁻ : ∀ a → isIso (f a)) (isSetA : isSet A) (isSetB : isSet B) where
  private
    isoover' : IsoOver (equivToIso (isoToEquiv isom)) P Q
    isoover' = equivOver→IsoOver (isoToEquiv isom) f λ a → isIsoToIsEquiv (f⁻ a)

    module P = hSetReasoning (A , isSetA) P
    module Q = hSetReasoning (B , isSetB) Q

  fiberwiseIsoOver→IsoOver : isIsoOver isom P Q f
  fiberwiseIsoOver→IsoOver .inv = λ b q → f⁻ (inv isom b) .fst (subst Q (sym $ rightInv isom b) q)
  fiberwiseIsoOver→IsoOver .rightInv = λ b q →
    f⁻ (inv isom b) .snd .fst (subst Q (λ i → rightInv isom b (~ i)) q)
    ◁ symP (subst-filler (λ z → z) (λ i → Q (rightInv isom b (~ i))) q)
  fiberwiseIsoOver→IsoOver .leftInv a p =
    P.Prectify $ P.≡out $
      f⁻cong∫~
        (sym (Q.reind-filler _) ∙ Q.reind-filler _ ∙ Q.reind-filler _ )
      ∙ P.reind-filler _
      ∙ P.≡in (isoover' .leftInv a p)
    where
      f⁻cong : ∀ {a a'}{q : Q (isom .fun a)}{q' : Q (isom .fun a')}
        (a≡a' : a ≡ a')
        → PathP (λ i → Q (fun isom (a≡a' i))) q q'
        → PathP (λ i → P (a≡a' i)) (f⁻ a .fst q) (f⁻ a' .fst q')
      f⁻cong a≡a' q≡q' = λ i → f⁻ (a≡a' i) .fst (q≡q' i)

      f⁻cong∫~ : ∀ {a a'}{q : Q (isom .fun a)}{q' : Q (isom .fun a')}
        → q Q.∫≡ q'
        → (f⁻ a .fst q) P.∫≡ (f⁻ a' .fst q')
      f⁻cong∫~ {a}{a'} q≡q' = P.≡in $
        f⁻cong a≡a' (Q.Prectify $ Q.≡out q≡q')
        where
          a≡a' : a ≡ a'
          a≡a' = isoFunInjective isom a a' (PathPΣ q≡q' .fst)
-- equivOver→isIsoOver {Q = Q}{isom = isom} f fEquiv =
--   isisoover (isoOver .inv) (isoOver .rightInv)
--     λ a p → {!isoOver .leftInv a p!}
--   where
--     isoOver : IsoOver (equivToIso $ isoToEquiv isom) _ Q
--     isoOver = equivOver→IsoOver (isoToEquiv isom) f fEquiv
