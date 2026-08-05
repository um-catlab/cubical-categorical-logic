module Cubical.Algebra.Instances.Monoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Constructions

private
  variable
    ℓ ℓX : Level

open AlgTheorySig
open AlgTheoryEqns

data MonOp : Type where
  εOp ·Op : MonOp

MonSig : AlgTheorySig ℓ-zero ℓ-zero
MonSig .ops = MonOp
MonSig .arities εOp = ⊥
MonSig .arities ·Op = Bool

data Three : Type where
  t0 t1 t2 : Three

data MonEq : Type where
  unitLE unitRE assocE : MonEq

MonVars : MonEq → Type
MonVars unitLE = Unit
MonVars unitRE = Unit
MonVars assocE = Three

sel : {X : Type ℓX} → X → X → Bool → X
sel x y true = x
sel x y false = y

module _ {V : Type} where
  tmε : Tm MonSig V
  tmε = node εOp (λ ())

  tm· : Tm MonSig V → Tm MonSig V → Tm MonSig V
  tm· s t = node ·Op (sel s t)

MonEqns : AlgTheoryEqns MonSig ℓ-zero ℓ-zero
MonEqns .eqns = MonEq
MonEqns .vars = MonVars
MonEqns .lhs unitLE = tm· tmε (var tt)
MonEqns .rhs unitLE = var tt
MonEqns .lhs unitRE = tm· (var tt) tmε
MonEqns .rhs unitRE = var tt
MonEqns .lhs assocE = tm· (tm· (var t0) (var t1)) (var t2)
MonEqns .rhs assocE = tm· (var t0) (tm· (var t1) (var t2))

data CommMonEq : Type where
  mon : MonEq → CommMonEq
  commE : CommMonEq

CommMonVars : CommMonEq → Type
CommMonVars (mon e) = MonVars e
CommMonVars commE = Bool

CommMonEqns : AlgTheoryEqns MonSig ℓ-zero ℓ-zero
CommMonEqns .eqns = CommMonEq
CommMonEqns .vars = CommMonVars
CommMonEqns .lhs (mon e) = MonEqns .lhs e
CommMonEqns .rhs (mon e) = MonEqns .rhs e
CommMonEqns .lhs commE = tm· (var true) (var false)
CommMonEqns .rhs commE = tm· (var false) (var true)

module MonNotation {X : Type ℓX} (B : Alg MonEqns X) where
  private module B = Alg B

  ε : X
  ε = B.⟨ εOp ⟩⟦ (λ ()) ⟧op

  infixl 30 _·_
  _·_ : X → X → X
  x · y = B.⟨ ·Op ⟩⟦ sel x y ⟧op

  -- interpretation commutes with the term-level operations only after a
  -- case split on the arity
  εTm : {V : Type} (ρ : V → X) → B.⟦ ρ ⟧Tm tmε ≡ ε
  εTm ρ = cong B.⟨ εOp ⟩⟦_⟧op (funExt (λ ()))

  ·Tm : {V : Type} (ρ : V → X) (s t : Tm MonSig V)
    → B.⟦ ρ ⟧Tm (tm· s t) ≡ B.⟦ ρ ⟧Tm s · B.⟦ ρ ⟧Tm t
  ·Tm ρ s t =
    cong B.⟨ ·Op ⟩⟦_⟧op (funExt (λ { true → refl ; false → refl }))

  unitL : ∀ x → ε · x ≡ x
  unitL x =
    cong (_· x) (sym (εTm (λ _ → x)))
    ∙ sym (·Tm (λ _ → x) tmε (var tt))
    ∙ B.⟦ unitLE ⟧eqn (λ _ → x)

  unitR : ∀ x → x · ε ≡ x
  unitR x =
    cong (x ·_) (sym (εTm (λ _ → x)))
    ∙ sym (·Tm (λ _ → x) (var tt) tmε)
    ∙ B.⟦ unitRE ⟧eqn (λ _ → x)

  assoc : ∀ x y z → (x · y) · z ≡ x · (y · z)
  assoc x y z =
    cong (_· z) (sym (·Tm ρ (var t0) (var t1)))
    ∙ sym (·Tm ρ (tm· (var t0) (var t1)) (var t2))
    ∙ B.⟦ assocE ⟧eqn ρ
    ∙ ·Tm ρ (var t0) (tm· (var t1) (var t2))
    ∙ cong (x ·_) (·Tm ρ (var t1) (var t2))
    where
      ρ : Three → X
      ρ t0 = x
      ρ t1 = y
      ρ t2 = z

selη : {X : Type ℓX} (g : Bool → X) → g ≡ sel (g true) (g false)
selη g = funExt (λ { true → refl ; false → refl })

Mon⊗Mon : AlgTheoryEqns (MonSig ⊕Sig MonSig) ℓ-zero ℓ-zero
Mon⊗Mon = ⊗Eqns ℓ-zero MonEqns MonEqns

module EckmannHilton {X : hSet ℓX} (B : Alg Mon⊗Mon ⟨ X ⟩) where
  private
    module B = Alg B
    Bσ = ⊗σModel ℓ-zero MonEqns MonEqns X B
    Bτ = ⊗τModel ℓ-zero MonEqns MonEqns X B
  open MonNotation Bσ public
  open MonNotation Bτ public
    renaming (ε to ε'; _·_ to _*_; unitL to unitL*;
              unitR to unitR*; assoc to assoc*;
              εTm to εTm*; ·Tm to ·Tm*)

  interchange : ∀ w x y z → (w * x) · (y * z) ≡ (w · y) * (x · z)
  interchange w x y z =
    cong B.⟨ inl ·Op ⟩⟦_⟧op (sym (selη _))
    ∙ B.⟦ inr (inr (·Op , ·Op)) ⟧eqn
        (λ p → sel (sel w x (p .lower .snd)) (sel y z (p .lower .snd))
                 (p .lower .fst))
    ∙ cong B.⟨ inr ·Op ⟩⟦_⟧op (selη _)

  ε≡ε' : ε ≡ ε'
  ε≡ε' =
    sym (unitL ε)
    ∙ cong₂ _·_ (sym (unitR* ε)) (sym (unitL* ε))
    ∙ interchange ε ε' ε' ε
    ∙ cong₂ _*_ (unitL ε') (unitR ε')
    ∙ unitL* ε'

  ·≡* : ∀ x y → x · y ≡ x * y
  ·≡* x y =
    cong₂ _·_ (sym (unitR* x)) (sym (unitL* y))
    ∙ interchange x ε' ε' y
    ∙ cong₂ _*_ (cong (x ·_) (sym ε≡ε') ∙ unitR x)
                (cong (_· y) (sym ε≡ε') ∙ unitL y)

  ·comm : ∀ x y → x · y ≡ y · x
  ·comm x y =
    cong₂ _·_ (sym (unitL* x)) (sym (unitR* y))
    ∙ interchange ε' x y ε'
    ∙ cong₂ _*_ (cong (_· y) (sym ε≡ε') ∙ unitL y)
                (cong (x ·_) (sym ε≡ε') ∙ unitR x)
    ∙ sym (·≡* y x)

  CommMonModel : Alg CommMonEqns ⟨ X ⟩
  CommMonModel .Alg.⟨_⟩⟦_⟧op = Alg.⟨_⟩⟦_⟧op Bσ
  CommMonModel .Alg.⟦_⟧eqn (mon e) = Alg.⟦_⟧eqn Bσ e
  CommMonModel .Alg.⟦_⟧eqn commE ρ =
    ·Tm ρ (var true) (var false)
    ∙ ·comm (ρ true) (ρ false)
    ∙ sym (·Tm ρ (var false) (var true))
