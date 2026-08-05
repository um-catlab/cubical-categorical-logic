-- The theories of rings and of commutative rings.
--
-- Written in the orientation the standard library's smart constructors
-- expect, so that both halves of `AlgIsoCommRingStr` are the axioms
-- themselves: a model of the theory *is* a `CommRingStr`, and a
-- homomorphism of models *is* an `IsCommRingHom`.
module Cubical.Algebra.Instances.Ring where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.CommRing.Base

open import Cubical.Categories.Category

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Arity
open import Cubical.Algebra.Theory.Category
open import Cubical.Algebra.Theory.Constructions

private
  variable
    ℓ ℓX : Level

open AlgTheorySig
open AlgTheoryEqns

data RingOp (ℓ : Level) : Type ℓ where
  0Op 1Op +Op ·Op -Op : RingOp ℓ

RingSig : (ℓ : Level) → AlgTheorySig ℓ ℓ
RingSig ℓ .ops = RingOp ℓ
RingSig ℓ .arities 0Op = A0 ℓ
RingSig ℓ .arities 1Op = A0 ℓ
RingSig ℓ .arities +Op = A2 ℓ
RingSig ℓ .arities ·Op = A2 ℓ
RingSig ℓ .arities -Op = A1 ℓ

module _ {ℓ} {V : Type ℓ} where
  tm0 : Tm (RingSig ℓ) V
  tm0 = node 0Op sel0

  tm1 : Tm (RingSig ℓ) V
  tm1 = node 1Op sel0

  tm+ : Tm (RingSig ℓ) V → Tm (RingSig ℓ) V → Tm (RingSig ℓ) V
  tm+ x y = node +Op (sel2 x y)

  tm· : Tm (RingSig ℓ) V → Tm (RingSig ℓ) V → Tm (RingSig ℓ) V
  tm· x y = node ·Op (sel2 x y)

  tm- : Tm (RingSig ℓ) V → Tm (RingSig ℓ) V
  tm- x = node -Op (sel1 x)

data RingEq (ℓ : Level) : Type ℓ where
  +assocE +idRE +invRE +commE : RingEq ℓ
  ·assocE ·idRE ·idLE ·distRE ·distLE : RingEq ℓ

RingVars : RingEq ℓ → Type ℓ
RingVars {ℓ} +assocE = A3 ℓ
RingVars {ℓ} +idRE = A1 ℓ
RingVars {ℓ} +invRE = A1 ℓ
RingVars {ℓ} +commE = A2 ℓ
RingVars {ℓ} ·assocE = A3 ℓ
RingVars {ℓ} ·idRE = A1 ℓ
RingVars {ℓ} ·idLE = A1 ℓ
RingVars {ℓ} ·distRE = A3 ℓ
RingVars {ℓ} ·distLE = A3 ℓ

RingEqns : (ℓ : Level) → AlgTheoryEqns (RingSig ℓ) ℓ ℓ
RingEqns ℓ .eqns = RingEq ℓ
RingEqns ℓ .vars = RingVars
RingEqns ℓ .lhs +assocE = tm+ (var p) (tm+ (var q) (var s))
RingEqns ℓ .rhs +assocE = tm+ (tm+ (var p) (var q)) (var s)
RingEqns ℓ .lhs +idRE = tm+ (var u) tm0
RingEqns ℓ .rhs +idRE = var u
RingEqns ℓ .lhs +invRE = tm+ (var u) (tm- (var u))
RingEqns ℓ .rhs +invRE = tm0
RingEqns ℓ .lhs +commE = tm+ (var l) (var r)
RingEqns ℓ .rhs +commE = tm+ (var r) (var l)
RingEqns ℓ .lhs ·assocE = tm· (var p) (tm· (var q) (var s))
RingEqns ℓ .rhs ·assocE = tm· (tm· (var p) (var q)) (var s)
RingEqns ℓ .lhs ·idRE = tm· (var u) tm1
RingEqns ℓ .rhs ·idRE = var u
RingEqns ℓ .lhs ·idLE = tm· tm1 (var u)
RingEqns ℓ .rhs ·idLE = var u
RingEqns ℓ .lhs ·distRE = tm· (var p) (tm+ (var q) (var s))
RingEqns ℓ .rhs ·distRE = tm+ (tm· (var p) (var q)) (tm· (var p) (var s))
RingEqns ℓ .lhs ·distLE = tm· (tm+ (var p) (var q)) (var s)
RingEqns ℓ .rhs ·distLE = tm+ (tm· (var p) (var s)) (tm· (var q) (var s))

data CommRingEq (ℓ : Level) : Type ℓ where
  rng : RingEq ℓ → CommRingEq ℓ
  ·commE : CommRingEq ℓ

CommRingVars : CommRingEq ℓ → Type ℓ
CommRingVars (rng e) = RingVars e
CommRingVars {ℓ} ·commE = A2 ℓ

CommRingEqns : (ℓ : Level) → AlgTheoryEqns (RingSig ℓ) ℓ ℓ
CommRingEqns ℓ .eqns = CommRingEq ℓ
CommRingEqns ℓ .vars = CommRingVars
CommRingEqns ℓ .lhs (rng e) = RingEqns ℓ .lhs e
CommRingEqns ℓ .rhs (rng e) = RingEqns ℓ .rhs e
CommRingEqns ℓ .lhs ·commE = tm· (var l) (var r)
CommRingEqns ℓ .rhs ·commE = tm· (var r) (var l)

-- The operations of a model of *any* theory over `RingSig`, with the
-- η-lemmas bridging a term former applied to a selector and the
-- operation itself.  The laws come later, once the equations are fixed.
module RingOps {ℓ} {X : Type ℓX} {σeq : AlgTheoryEqns (RingSig ℓ) ℓ ℓ}
  (B : Alg σeq X) where
  private module B = Alg B

  0r : X
  0r = B.⟨ 0Op ⟩⟦ sel0 ⟧op

  1r : X
  1r = B.⟨ 1Op ⟩⟦ sel0 ⟧op

  infixl 30 _+_
  _+_ : X → X → X
  x + y = B.⟨ +Op ⟩⟦ sel2 x y ⟧op

  infixl 40 _·_
  _·_ : X → X → X
  x · y = B.⟨ ·Op ⟩⟦ sel2 x y ⟧op

  -_ : X → X
  - x = B.⟨ -Op ⟩⟦ sel1 x ⟧op

  module _ {V : Type ℓ} (ρ : V → X) where
    0Tm : B.⟦ ρ ⟧Tm tm0 ≡ 0r
    0Tm = cong B.⟨ 0Op ⟩⟦_⟧op (sel0η _)

    1Tm : B.⟦ ρ ⟧Tm tm1 ≡ 1r
    1Tm = cong B.⟨ 1Op ⟩⟦_⟧op (sel0η _)

    +Tm : (x y : Tm (RingSig ℓ) V)
      → B.⟦ ρ ⟧Tm (tm+ x y) ≡ B.⟦ ρ ⟧Tm x + B.⟦ ρ ⟧Tm y
    +Tm x y = cong B.⟨ +Op ⟩⟦_⟧op (sel2η _)

    ·Tm : (x y : Tm (RingSig ℓ) V)
      → B.⟦ ρ ⟧Tm (tm· x y) ≡ B.⟦ ρ ⟧Tm x · B.⟦ ρ ⟧Tm y
    ·Tm x y = cong B.⟨ ·Op ⟩⟦_⟧op (sel2η _)

    -Tm : (x : Tm (RingSig ℓ) V)
      → B.⟦ ρ ⟧Tm (tm- x) ≡ - (B.⟦ ρ ⟧Tm x)
    -Tm x = cong B.⟨ -Op ⟩⟦_⟧op (sel1η _)

module RingNotation {ℓ} {X : Type ℓX} (B : Alg (RingEqns ℓ) X) where
  private module B = Alg B
  open RingOps B public

  +Assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
  +Assoc x y z =
    cong (x +_) (sym (+Tm ρ (var q) (var s)))
    ∙ sym (+Tm ρ (var p) (tm+ (var q) (var s)))
    ∙ B.⟦ +assocE ⟧eqn ρ
    ∙ +Tm ρ (tm+ (var p) (var q)) (var s)
    ∙ cong (_+ z) (+Tm ρ (var p) (var q))
    where ρ = sel3 x y z

  +IdR : ∀ x → x + 0r ≡ x
  +IdR x =
    cong (x +_) (sym (0Tm ρ))
    ∙ sym (+Tm ρ (var u) tm0)
    ∙ B.⟦ +idRE ⟧eqn ρ
    where ρ = sel1 x

  +InvR : ∀ x → x + (- x) ≡ 0r
  +InvR x =
    cong (x +_) (sym (-Tm ρ (var u)))
    ∙ sym (+Tm ρ (var u) (tm- (var u)))
    ∙ B.⟦ +invRE ⟧eqn ρ
    ∙ 0Tm ρ
    where ρ = sel1 x

  +Comm : ∀ x y → x + y ≡ y + x
  +Comm x y =
    sym (+Tm ρ (var l) (var r))
    ∙ B.⟦ +commE ⟧eqn ρ
    ∙ +Tm ρ (var r) (var l)
    where ρ = sel2 x y

  ·Assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
  ·Assoc x y z =
    cong (x ·_) (sym (·Tm ρ (var q) (var s)))
    ∙ sym (·Tm ρ (var p) (tm· (var q) (var s)))
    ∙ B.⟦ ·assocE ⟧eqn ρ
    ∙ ·Tm ρ (tm· (var p) (var q)) (var s)
    ∙ cong (_· z) (·Tm ρ (var p) (var q))
    where ρ = sel3 x y z

  ·IdR : ∀ x → x · 1r ≡ x
  ·IdR x =
    cong (x ·_) (sym (1Tm ρ))
    ∙ sym (·Tm ρ (var u) tm1)
    ∙ B.⟦ ·idRE ⟧eqn ρ
    where ρ = sel1 x

  ·IdL : ∀ x → 1r · x ≡ x
  ·IdL x =
    cong (_· x) (sym (1Tm ρ))
    ∙ sym (·Tm ρ tm1 (var u))
    ∙ B.⟦ ·idLE ⟧eqn ρ
    where ρ = sel1 x

  ·DistR+ : ∀ x y z → x · (y + z) ≡ (x · y) + (x · z)
  ·DistR+ x y z =
    cong (x ·_) (sym (+Tm ρ (var q) (var s)))
    ∙ sym (·Tm ρ (var p) (tm+ (var q) (var s)))
    ∙ B.⟦ ·distRE ⟧eqn ρ
    ∙ +Tm ρ (tm· (var p) (var q)) (tm· (var p) (var s))
    ∙ cong₂ _+_ (·Tm ρ (var p) (var q)) (·Tm ρ (var p) (var s))
    where ρ = sel3 x y z

  ·DistL+ : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
  ·DistL+ x y z =
    cong (_· z) (sym (+Tm ρ (var p) (var q)))
    ∙ sym (·Tm ρ (tm+ (var p) (var q)) (var s))
    ∙ B.⟦ ·distLE ⟧eqn ρ
    ∙ +Tm ρ (tm· (var p) (var s)) (tm· (var q) (var s))
    ∙ cong₂ _+_ (·Tm ρ (var p) (var s)) (·Tm ρ (var q) (var s))
    where ρ = sel3 x y z

module CommRingNotation {ℓ} {X : Type ℓX} (B : Alg (CommRingEqns ℓ) X) where
  private
    module B = Alg B

    Brng : Alg (RingEqns ℓ) X
    Brng .Alg.⟨_⟩⟦_⟧op = B.⟨_⟩⟦_⟧op
    Brng .Alg.⟦_⟧eqn e = B.⟦ rng e ⟧eqn

  open RingNotation Brng public

  ·Comm : ∀ x y → x · y ≡ y · x
  ·Comm x y =
    sym (·Tm ρ (var l) (var r))
    ∙ B.⟦ ·commE ⟧eqn ρ
    ∙ ·Tm ρ (var r) (var l)
    where ρ = sel2 x y

-- Models are (commutative) ring structures.
module _ {ℓ} {X : Type ℓ} (isSetX : isSet X) where

  AlgRingStr : Alg (RingEqns ℓ) X → RingStr X
  AlgRingStr B .RingStr.0r = 0r where open RingNotation B
  AlgRingStr B .RingStr.1r = 1r where open RingNotation B
  AlgRingStr B .RingStr._+_ = _+_ where open RingNotation B
  AlgRingStr B .RingStr._·_ = _·_ where open RingNotation B
  AlgRingStr B .RingStr.-_ = -_ where open RingNotation B
  AlgRingStr B .RingStr.isRing =
    makeIsRing isSetX +Assoc +IdR +InvR +Comm
      ·Assoc ·IdR ·IdL ·DistR+ ·DistL+
    where open RingNotation B

  RingStrAlg : RingStr X → Alg (RingEqns ℓ) X
  RingStrAlg R .Alg.⟨_⟩⟦_⟧op 0Op _ = R .RingStr.0r
  RingStrAlg R .Alg.⟨_⟩⟦_⟧op 1Op _ = R .RingStr.1r
  RingStrAlg R .Alg.⟨_⟩⟦_⟧op +Op g = RingStr._+_ R (g l) (g r)
  RingStrAlg R .Alg.⟨_⟩⟦_⟧op ·Op g = RingStr._·_ R (g l) (g r)
  RingStrAlg R .Alg.⟨_⟩⟦_⟧op -Op g = RingStr.-_ R (g u)
  RingStrAlg R .Alg.⟦_⟧eqn +assocE ρ = RingStr.+Assoc R (ρ p) (ρ q) (ρ s)
  RingStrAlg R .Alg.⟦_⟧eqn +idRE ρ = RingStr.+IdR R (ρ u)
  RingStrAlg R .Alg.⟦_⟧eqn +invRE ρ = RingStr.+InvR R (ρ u)
  RingStrAlg R .Alg.⟦_⟧eqn +commE ρ = RingStr.+Comm R (ρ l) (ρ r)
  RingStrAlg R .Alg.⟦_⟧eqn ·assocE ρ = RingStr.·Assoc R (ρ p) (ρ q) (ρ s)
  RingStrAlg R .Alg.⟦_⟧eqn ·idRE ρ = RingStr.·IdR R (ρ u)
  RingStrAlg R .Alg.⟦_⟧eqn ·idLE ρ = RingStr.·IdL R (ρ u)
  RingStrAlg R .Alg.⟦_⟧eqn ·distRE ρ = RingStr.·DistR+ R (ρ p) (ρ q) (ρ s)
  RingStrAlg R .Alg.⟦_⟧eqn ·distLE ρ = RingStr.·DistL+ R (ρ p) (ρ q) (ρ s)

  private
    opsExt : (B : Alg (RingEqns ℓ) X)
      → Alg.⟨_⟩⟦_⟧op (RingStrAlg (AlgRingStr B)) ≡ Alg.⟨_⟩⟦_⟧op B
    opsExt B = funExt λ
      { 0Op → funExt λ g → cong B.⟨ 0Op ⟩⟦_⟧op (sym (sel0η g))
      ; 1Op → funExt λ g → cong B.⟨ 1Op ⟩⟦_⟧op (sym (sel0η g))
      ; +Op → funExt λ g → cong B.⟨ +Op ⟩⟦_⟧op (sym (sel2η g))
      ; ·Op → funExt λ g → cong B.⟨ ·Op ⟩⟦_⟧op (sym (sel2η g))
      ; -Op → funExt λ g → cong B.⟨ -Op ⟩⟦_⟧op (sym (sel1η g)) }
      where module B = Alg B

  AlgIsoRingStr : Iso (Alg (RingEqns ℓ) X) (RingStr X)
  AlgIsoRingStr .Iso.fun = AlgRingStr
  AlgIsoRingStr .Iso.inv = RingStrAlg
  AlgIsoRingStr .Iso.sec R i .RingStr.0r = R .RingStr.0r
  AlgIsoRingStr .Iso.sec R i .RingStr.1r = R .RingStr.1r
  AlgIsoRingStr .Iso.sec R i .RingStr._+_ = R .RingStr._+_
  AlgIsoRingStr .Iso.sec R i .RingStr._·_ = R .RingStr._·_
  AlgIsoRingStr .Iso.sec R i .RingStr.-_ = R .RingStr.-_
  AlgIsoRingStr .Iso.sec R i .RingStr.isRing =
    isPropIsRing _ _ _ _ _
      (AlgRingStr (RingStrAlg R) .RingStr.isRing) (R .RingStr.isRing) i
  AlgIsoRingStr .Iso.ret B = AlgExt isSetX (opsExt B)

  AlgCommRingStr : Alg (CommRingEqns ℓ) X → CommRingStr X
  AlgCommRingStr B .CommRingStr.0r = 0r where open CommRingNotation B
  AlgCommRingStr B .CommRingStr.1r = 1r where open CommRingNotation B
  AlgCommRingStr B .CommRingStr._+_ = _+_ where open CommRingNotation B
  AlgCommRingStr B .CommRingStr._·_ = _·_ where open CommRingNotation B
  AlgCommRingStr B .CommRingStr.-_ = -_ where open CommRingNotation B
  AlgCommRingStr B .CommRingStr.isCommRing =
    makeIsCommRing isSetX +Assoc +IdR +InvR +Comm ·Assoc ·IdR ·DistR+ ·Comm
    where open CommRingNotation B

  CommRingStrAlg : CommRingStr X → Alg (CommRingEqns ℓ) X
  CommRingStrAlg R .Alg.⟨_⟩⟦_⟧op =
    Alg.⟨_⟩⟦_⟧op (RingStrAlg (CommRingStr→RingStr R))
  CommRingStrAlg R .Alg.⟦_⟧eqn (rng e) =
    Alg.⟦_⟧eqn (RingStrAlg (CommRingStr→RingStr R)) e
  CommRingStrAlg R .Alg.⟦_⟧eqn ·commE ρ = CommRingStr.·Comm R (ρ l) (ρ r)

  AlgIsoCommRingStr : Iso (Alg (CommRingEqns ℓ) X) (CommRingStr X)
  AlgIsoCommRingStr .Iso.fun = AlgCommRingStr
  AlgIsoCommRingStr .Iso.inv = CommRingStrAlg
  AlgIsoCommRingStr .Iso.sec R i .CommRingStr.0r = R .CommRingStr.0r
  AlgIsoCommRingStr .Iso.sec R i .CommRingStr.1r = R .CommRingStr.1r
  AlgIsoCommRingStr .Iso.sec R i .CommRingStr._+_ = R .CommRingStr._+_
  AlgIsoCommRingStr .Iso.sec R i .CommRingStr._·_ = R .CommRingStr._·_
  AlgIsoCommRingStr .Iso.sec R i .CommRingStr.-_ = R .CommRingStr.-_
  AlgIsoCommRingStr .Iso.sec R i .CommRingStr.isCommRing =
    isPropIsCommRing _ _ _ _ _
      (AlgCommRingStr (CommRingStrAlg R) .CommRingStr.isCommRing)
      (R .CommRingStr.isCommRing) i
  AlgIsoCommRingStr .Iso.ret B = AlgExt isSetX (funExt λ
    { 0Op → funExt λ g → cong B.⟨ 0Op ⟩⟦_⟧op (sym (sel0η g))
    ; 1Op → funExt λ g → cong B.⟨ 1Op ⟩⟦_⟧op (sym (sel0η g))
    ; +Op → funExt λ g → cong B.⟨ +Op ⟩⟦_⟧op (sym (sel2η g))
    ; ·Op → funExt λ g → cong B.⟨ ·Op ⟩⟦_⟧op (sym (sel2η g))
    ; -Op → funExt λ g → cong B.⟨ -Op ⟩⟦_⟧op (sym (sel1η g)) })
    where module B = Alg B

-- Homomorphisms of models are ring homomorphisms.
module _ {ℓ} {X Y : Type ℓ} (isSetX : isSet X) (isSetY : isSet Y)
  (B : Alg (CommRingEqns ℓ) X) (C : Alg (CommRingEqns ℓ) Y) {f : X → Y}
  where

  private
    module B = Alg B
    module C = Alg C

  HomoIsCommRingHom : Homo (CommRingEqns ℓ) f B C
    → IsCommRingHom (AlgCommRingStr isSetX B) f (AlgCommRingStr isSetY C)
  HomoIsCommRingHom ϕ .IsCommRingHom.pres0 =
    Homo.op-hom' ϕ 0Op sel0 ∙ cong C.⟨ 0Op ⟩⟦_⟧op (funExt λ ())
  HomoIsCommRingHom ϕ .IsCommRingHom.pres1 =
    Homo.op-hom' ϕ 1Op sel0 ∙ cong C.⟨ 1Op ⟩⟦_⟧op (funExt λ ())
  HomoIsCommRingHom ϕ .IsCommRingHom.pres+ x y =
    Homo.op-hom' ϕ +Op (sel2 x y)
    ∙ cong C.⟨ +Op ⟩⟦_⟧op (funExt λ { l → refl ; r → refl })
  HomoIsCommRingHom ϕ .IsCommRingHom.pres· x y =
    Homo.op-hom' ϕ ·Op (sel2 x y)
    ∙ cong C.⟨ ·Op ⟩⟦_⟧op (funExt λ { l → refl ; r → refl })
  HomoIsCommRingHom ϕ .IsCommRingHom.pres- x =
    Homo.op-hom' ϕ -Op (sel1 x)
    ∙ cong C.⟨ -Op ⟩⟦_⟧op (funExt λ { u → refl })

  IsCommRingHomHomo
    : IsCommRingHom (AlgCommRingStr isSetX B) f (AlgCommRingStr isSetY C)
    → Homo (CommRingEqns ℓ) f B C
  IsCommRingHomHomo ψ .Homo.op-hom 0Op x y eq =
    cong f eq
    ∙ cong f (cong B.⟨ 0Op ⟩⟦_⟧op (sel0η x))
    ∙ ψ .IsCommRingHom.pres0
    ∙ cong C.⟨ 0Op ⟩⟦_⟧op (sym (sel0η _))
  IsCommRingHomHomo ψ .Homo.op-hom 1Op x y eq =
    cong f eq
    ∙ cong f (cong B.⟨ 1Op ⟩⟦_⟧op (sel0η x))
    ∙ ψ .IsCommRingHom.pres1
    ∙ cong C.⟨ 1Op ⟩⟦_⟧op (sym (sel0η _))
  IsCommRingHomHomo ψ .Homo.op-hom +Op x y eq =
    cong f eq
    ∙ cong f (cong B.⟨ +Op ⟩⟦_⟧op (sel2η x))
    ∙ ψ .IsCommRingHom.pres+ (x l) (x r)
    ∙ cong C.⟨ +Op ⟩⟦_⟧op (sym (sel2η _))
  IsCommRingHomHomo ψ .Homo.op-hom ·Op x y eq =
    cong f eq
    ∙ cong f (cong B.⟨ ·Op ⟩⟦_⟧op (sel2η x))
    ∙ ψ .IsCommRingHom.pres· (x l) (x r)
    ∙ cong C.⟨ ·Op ⟩⟦_⟧op (sym (sel2η _))
  IsCommRingHomHomo ψ .Homo.op-hom -Op x y eq =
    cong f eq
    ∙ cong f (cong B.⟨ -Op ⟩⟦_⟧op (sel1η x))
    ∙ ψ .IsCommRingHom.pres- (x u)
    ∙ cong C.⟨ -Op ⟩⟦_⟧op (sym (sel1η _))

  HomoIsoIsCommRingHom : Iso (Homo (CommRingEqns ℓ) f B C)
    (IsCommRingHom (AlgCommRingStr isSetX B) f (AlgCommRingStr isSetY C))
  HomoIsoIsCommRingHom .Iso.fun = HomoIsCommRingHom
  HomoIsoIsCommRingHom .Iso.inv = IsCommRingHomHomo
  HomoIsoIsCommRingHom .Iso.sec ψ = isPropIsCommRingHom _ _ _ _ ψ
  HomoIsoIsCommRingHom .Iso.ret ϕ =
    isPropHomo (CommRingEqns ℓ) isSetY _ ϕ

RING : (ℓ ℓX : Level) → Category _ _
RING ℓ ℓX = MOD (RingEqns ℓ) ℓX

COMMRING : (ℓ ℓX : Level) → Category _ _
COMMRING ℓ ℓX = MOD (CommRingEqns ℓ) ℓX
