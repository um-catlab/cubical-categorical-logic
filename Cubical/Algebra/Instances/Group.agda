-- The theories of groups and of abelian groups.
--
-- `MOD GroupEqns` is the category of groups: its objects are exactly
-- `GroupStr`s (`AlgIsoGroupStr`) and its morphisms exactly the group
-- homomorphisms (`HomoIsoIsGroupHom`), so everything the framework
-- proves about categories of models -- free models, initiality,
-- displayed models as logical relations -- applies to groups verbatim.
module Cubical.Algebra.Instances.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Monoid.Base

open import Cubical.Categories.Category

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Arity
open import Cubical.Algebra.Theory.Category
open import Cubical.Algebra.Theory.Constructions

private
  variable
    ℓ ℓX ℓY : Level

open AlgTheorySig
open AlgTheoryEqns

data GroupOp (ℓ : Level) : Type ℓ where
  εOp ·Op invOp : GroupOp ℓ

GroupSig : (ℓ : Level) → AlgTheorySig ℓ ℓ
GroupSig ℓ .ops = GroupOp ℓ
GroupSig ℓ .arities εOp = A0 ℓ
GroupSig ℓ .arities ·Op = A2 ℓ
GroupSig ℓ .arities invOp = A1 ℓ

module _ {ℓ} {V : Type ℓ} where
  tmε : Tm (GroupSig ℓ) V
  tmε = node εOp sel0

  tm· : Tm (GroupSig ℓ) V → Tm (GroupSig ℓ) V → Tm (GroupSig ℓ) V
  tm· x y = node ·Op (sel2 x y)

  tminv : Tm (GroupSig ℓ) V → Tm (GroupSig ℓ) V
  tminv x = node invOp (sel1 x)

data GroupEq (ℓ : Level) : Type ℓ where
  unitLE unitRE assocE invLE invRE : GroupEq ℓ

GroupVars : GroupEq ℓ → Type ℓ
GroupVars {ℓ} unitLE = A1 ℓ
GroupVars {ℓ} unitRE = A1 ℓ
GroupVars {ℓ} assocE = A3 ℓ
GroupVars {ℓ} invLE = A1 ℓ
GroupVars {ℓ} invRE = A1 ℓ

GroupEqns : (ℓ : Level) → AlgTheoryEqns (GroupSig ℓ) ℓ ℓ
GroupEqns ℓ .eqns = GroupEq ℓ
GroupEqns ℓ .vars = GroupVars
GroupEqns ℓ .lhs unitLE = tm· tmε (var u)
GroupEqns ℓ .rhs unitLE = var u
GroupEqns ℓ .lhs unitRE = tm· (var u) tmε
GroupEqns ℓ .rhs unitRE = var u
GroupEqns ℓ .lhs assocE = tm· (tm· (var p) (var q)) (var s)
GroupEqns ℓ .rhs assocE = tm· (var p) (tm· (var q) (var s))
GroupEqns ℓ .lhs invLE = tm· (tminv (var u)) (var u)
GroupEqns ℓ .rhs invLE = tmε
GroupEqns ℓ .lhs invRE = tm· (var u) (tminv (var u))
GroupEqns ℓ .rhs invRE = tmε

data AbGroupEq (ℓ : Level) : Type ℓ where
  grp : GroupEq ℓ → AbGroupEq ℓ
  commE : AbGroupEq ℓ

AbGroupVars : AbGroupEq ℓ → Type ℓ
AbGroupVars (grp e) = GroupVars e
AbGroupVars {ℓ} commE = A2 ℓ

AbGroupEqns : (ℓ : Level) → AlgTheoryEqns (GroupSig ℓ) ℓ ℓ
AbGroupEqns ℓ .eqns = AbGroupEq ℓ
AbGroupEqns ℓ .vars = AbGroupVars
AbGroupEqns ℓ .lhs (grp e) = GroupEqns ℓ .lhs e
AbGroupEqns ℓ .rhs (grp e) = GroupEqns ℓ .rhs e
AbGroupEqns ℓ .lhs commE = tm· (var l) (var r)
AbGroupEqns ℓ .rhs commE = tm· (var r) (var l)

-- The operations and the derived laws of a model.  Every step is the
-- model's own equation, sandwiched between the η-lemmas that identify a
-- term former applied to a selector with the operation itself.
module GroupNotation {ℓ} {X : Type ℓX} (B : Alg (GroupEqns ℓ) X) where
  private module B = Alg B

  ε : X
  ε = B.⟨ εOp ⟩⟦ sel0 ⟧op

  infixl 30 _·_
  _·_ : X → X → X
  x · y = B.⟨ ·Op ⟩⟦ sel2 x y ⟧op

  inv : X → X
  inv x = B.⟨ invOp ⟩⟦ sel1 x ⟧op

  εTm : {V : Type ℓ} (ρ : V → X) → B.⟦ ρ ⟧Tm tmε ≡ ε
  εTm ρ = cong B.⟨ εOp ⟩⟦_⟧op (sel0η _)

  ·Tm : {V : Type ℓ} (ρ : V → X) (x y : Tm (GroupSig ℓ) V)
    → B.⟦ ρ ⟧Tm (tm· x y) ≡ B.⟦ ρ ⟧Tm x · B.⟦ ρ ⟧Tm y
  ·Tm ρ x y = cong B.⟨ ·Op ⟩⟦_⟧op (sel2η _)

  invTm : {V : Type ℓ} (ρ : V → X) (x : Tm (GroupSig ℓ) V)
    → B.⟦ ρ ⟧Tm (tminv x) ≡ inv (B.⟦ ρ ⟧Tm x)
  invTm ρ x = cong B.⟨ invOp ⟩⟦_⟧op (sel1η _)

  unitL : ∀ x → ε · x ≡ x
  unitL x =
    cong (_· x) (sym (εTm ρ))
    ∙ sym (·Tm ρ tmε (var u))
    ∙ B.⟦ unitLE ⟧eqn ρ
    where ρ = sel1 x

  unitR : ∀ x → x · ε ≡ x
  unitR x =
    cong (x ·_) (sym (εTm ρ))
    ∙ sym (·Tm ρ (var u) tmε)
    ∙ B.⟦ unitRE ⟧eqn ρ
    where ρ = sel1 x

  assoc : ∀ x y z → (x · y) · z ≡ x · (y · z)
  assoc x y z =
    cong (_· z) (sym (·Tm ρ (var p) (var q)))
    ∙ sym (·Tm ρ (tm· (var p) (var q)) (var s))
    ∙ B.⟦ assocE ⟧eqn ρ
    ∙ ·Tm ρ (var p) (tm· (var q) (var s))
    ∙ cong (x ·_) (·Tm ρ (var q) (var s))
    where ρ = sel3 x y z

  invL : ∀ x → inv x · x ≡ ε
  invL x =
    cong (_· x) (sym (invTm ρ (var u)))
    ∙ sym (·Tm ρ (tminv (var u)) (var u))
    ∙ B.⟦ invLE ⟧eqn ρ
    ∙ εTm ρ
    where ρ = sel1 x

  invR : ∀ x → x · inv x ≡ ε
  invR x =
    cong (x ·_) (sym (invTm ρ (var u)))
    ∙ sym (·Tm ρ (var u) (tminv (var u)))
    ∙ B.⟦ invRE ⟧eqn ρ
    ∙ εTm ρ
    where ρ = sel1 x

module AbGroupNotation {ℓ} {X : Type ℓX} (B : Alg (AbGroupEqns ℓ) X) where
  private
    module B = Alg B

    Bgrp : Alg (GroupEqns ℓ) X
    Bgrp .Alg.⟨_⟩⟦_⟧op = B.⟨_⟩⟦_⟧op
    Bgrp .Alg.⟦_⟧eqn e = B.⟦ grp e ⟧eqn

  open GroupNotation Bgrp public

  ·Comm : ∀ x y → x · y ≡ y · x
  ·Comm x y =
    sym (·Tm ρ (var l) (var r))
    ∙ B.⟦ commE ⟧eqn ρ
    ∙ ·Tm ρ (var r) (var l)
    where ρ = sel2 x y

-- Models are group structures.
module _ {ℓ} {X : Type ℓX} (isSetX : isSet X) where

  AlgGroupStr : Alg (GroupEqns ℓ) X → GroupStr X
  AlgGroupStr B .GroupStr.1g = ε
    where open GroupNotation B
  AlgGroupStr B .GroupStr._·_ = _·_
    where open GroupNotation B
  AlgGroupStr B .GroupStr.inv = inv
    where open GroupNotation B
  AlgGroupStr B .GroupStr.isGroup =
    makeIsGroup isSetX (λ x y z → sym (assoc x y z)) unitR unitL invR invL
    where open GroupNotation B

  GroupStrAlg : GroupStr X → Alg (GroupEqns ℓ) X
  GroupStrAlg G .Alg.⟨_⟩⟦_⟧op εOp _ = G .GroupStr.1g
  GroupStrAlg G .Alg.⟨_⟩⟦_⟧op ·Op g = GroupStr._·_ G (g l) (g r)
  GroupStrAlg G .Alg.⟨_⟩⟦_⟧op invOp g = G .GroupStr.inv (g u)
  GroupStrAlg G .Alg.⟦_⟧eqn unitLE ρ = GroupStr.·IdL G (ρ u)
  GroupStrAlg G .Alg.⟦_⟧eqn unitRE ρ = GroupStr.·IdR G (ρ u)
  GroupStrAlg G .Alg.⟦_⟧eqn assocE ρ =
    sym (GroupStr.·Assoc G (ρ p) (ρ q) (ρ s))
  GroupStrAlg G .Alg.⟦_⟧eqn invLE ρ = GroupStr.·InvL G (ρ u)
  GroupStrAlg G .Alg.⟦_⟧eqn invRE ρ = GroupStr.·InvR G (ρ u)

  AlgIsoGroupStr : Iso (Alg (GroupEqns ℓ) X) (GroupStr X)
  AlgIsoGroupStr .Iso.fun = AlgGroupStr
  AlgIsoGroupStr .Iso.inv = GroupStrAlg
  AlgIsoGroupStr .Iso.sec G i .GroupStr.1g = G .GroupStr.1g
  AlgIsoGroupStr .Iso.sec G i .GroupStr._·_ = G .GroupStr._·_
  AlgIsoGroupStr .Iso.sec G i .GroupStr.inv = G .GroupStr.inv
  AlgIsoGroupStr .Iso.sec G i .GroupStr.isGroup =
    isPropIsGroup _ _ _
      (AlgGroupStr (GroupStrAlg G) .GroupStr.isGroup)
      (G .GroupStr.isGroup) i
  AlgIsoGroupStr .Iso.ret B =
    AlgExt isSetX (funExt λ
      { εOp → funExt λ g → cong B.⟨ εOp ⟩⟦_⟧op (sym (sel0η g))
      ; ·Op → funExt λ g → cong B.⟨ ·Op ⟩⟦_⟧op (sym (sel2η g))
      ; invOp → funExt λ g → cong B.⟨ invOp ⟩⟦_⟧op (sym (sel1η g)) })
    where module B = Alg B

-- Homomorphisms of models are group homomorphisms.
module _ {ℓ} {X Y : Type ℓ} (isSetX : isSet X) (isSetY : isSet Y)
  (B : Alg (GroupEqns ℓ) X) (C : Alg (GroupEqns ℓ) Y) {f : X → Y} where

  private
    module B = Alg B
    module C = Alg C

  HomoIsGroupHom : Homo (GroupEqns ℓ) f B C
    → IsGroupHom (AlgGroupStr isSetX B) f (AlgGroupStr isSetY C)
  HomoIsGroupHom ϕ .IsGroupHom.pres· x y =
    Homo.op-hom' ϕ ·Op (sel2 x y)
    ∙ cong C.⟨ ·Op ⟩⟦_⟧op (funExt λ { l → refl ; r → refl })
  HomoIsGroupHom ϕ .IsGroupHom.pres1 =
    Homo.op-hom' ϕ εOp sel0
    ∙ cong C.⟨ εOp ⟩⟦_⟧op (funExt λ ())
  HomoIsGroupHom ϕ .IsGroupHom.presinv x =
    Homo.op-hom' ϕ invOp (sel1 x)
    ∙ cong C.⟨ invOp ⟩⟦_⟧op (funExt λ { u → refl })

  IsGroupHomHomo : IsGroupHom (AlgGroupStr isSetX B) f (AlgGroupStr isSetY C)
    → Homo (GroupEqns ℓ) f B C
  IsGroupHomHomo ψ .Homo.op-hom εOp x y eq =
    cong f eq
    ∙ cong f (cong B.⟨ εOp ⟩⟦_⟧op (sel0η x))
    ∙ ψ .IsGroupHom.pres1
    ∙ cong C.⟨ εOp ⟩⟦_⟧op (sym (sel0η _))
  IsGroupHomHomo ψ .Homo.op-hom ·Op x y eq =
    cong f eq
    ∙ cong f (cong B.⟨ ·Op ⟩⟦_⟧op (sel2η x))
    ∙ ψ .IsGroupHom.pres· (x l) (x r)
    ∙ cong C.⟨ ·Op ⟩⟦_⟧op (sym (sel2η _))
  IsGroupHomHomo ψ .Homo.op-hom invOp x y eq =
    cong f eq
    ∙ cong f (cong B.⟨ invOp ⟩⟦_⟧op (sel1η x))
    ∙ ψ .IsGroupHom.presinv (x u)
    ∙ cong C.⟨ invOp ⟩⟦_⟧op (sym (sel1η _))

  HomoIsoIsGroupHom : Iso (Homo (GroupEqns ℓ) f B C)
    (IsGroupHom (AlgGroupStr isSetX B) f (AlgGroupStr isSetY C))
  HomoIsoIsGroupHom .Iso.fun = HomoIsGroupHom
  HomoIsoIsGroupHom .Iso.inv = IsGroupHomHomo
  HomoIsoIsGroupHom .Iso.sec ψ = isPropIsGroupHom _ _ _ ψ
  HomoIsoIsGroupHom .Iso.ret ϕ = isPropHomo (GroupEqns ℓ) isSetY _ ϕ

-- The category of groups, and the category of abelian groups.
GROUP : (ℓ ℓX : Level) → Category _ _
GROUP ℓ ℓX = MOD (GroupEqns ℓ) ℓX

ABGROUP : (ℓ ℓX : Level) → Category _ _
ABGROUP ℓ ℓX = MOD (AbGroupEqns ℓ) ℓX
