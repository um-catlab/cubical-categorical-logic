module Cubical.Algebra.Instances.State where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.More

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Algebra.Theory
import Cubical.Algebra.State as S

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰ'' : Level

open AlgTheorySig
open AlgTheoryEqns

data StateOps : Type where
  rdOp : StateOps
  wtOp : Bool → StateOps

StateSig : AlgTheorySig ℓ-zero ℓ-zero
StateSig .ops = StateOps
StateSig .arities rdOp = Bool
StateSig .arities (wtOp b) = Unit

data StateEqns : Type where
  wt-rdE : Bool → StateEqns
  rd-wtE : StateEqns
  wt-wtE : Bool → Bool → StateEqns

StateVars : StateEqns → Type
StateVars (wt-rdE _) = Bool
StateVars rd-wtE = Unit
StateVars (wt-wtE _ _) = Unit

StateTheory : AlgTheoryEqns StateSig ℓ-zero ℓ-zero
StateTheory .eqns = StateEqns
StateTheory .vars = StateVars
StateTheory .lhs (wt-rdE b) = node (wtOp b) (λ _ → node rdOp var)
StateTheory .rhs (wt-rdE b) = node (wtOp b) (λ _ → var b)
StateTheory .lhs rd-wtE = var tt
StateTheory .rhs rd-wtE = node rdOp (λ c → node (wtOp c) (λ _ → var tt))
StateTheory .lhs (wt-wtE b1 b2) =
  node (wtOp b1) (λ _ → node (wtOp b2) (λ _ → var tt))
StateTheory .rhs (wt-wtE b1 b2) = node (wtOp b2) (λ _ → var tt)

StateAlg : Type ℓ → Type ℓ
StateAlg = Alg StateTheory

module StateAlgNotation {X : Type ℓ} (B : StateAlg X) where
  private module B = Alg B

  rd' : (Bool → X) → X
  rd' = B.⟨ rdOp ⟩⟦_⟧op

  rd : X → X → X
  rd xt xf = rd' (λ c → if c then xt else xf)

  wt : Bool → X → X
  wt b x = B.⟨ wtOp b ⟩⟦ (λ _ → x) ⟧op

  wt-rd : ∀ b xt xf → wt b (rd xt xf) ≡ wt b (if b then xt else xf)
  wt-rd b xt xf = B.⟦ wt-rdE b ⟧eqn (λ c → if c then xt else xf)

  wt-wt : ∀ b1 b2 x → (wt b1 $ wt b2 x) ≡ wt b2 x
  wt-wt b1 b2 x = B.⟦ wt-wtE b1 b2 ⟧eqn (λ _ → x)

  rd-wt' : ∀ x → x ≡ rd' (λ c → wt c x)
  rd-wt' x = B.⟦ rd-wtE ⟧eqn (λ _ → x)

  rd-wt : ∀ x → x ≡ rd (wt true x) (wt false x)
  rd-wt x = rd-wt' x ∙ cong rd' (funExt λ { true → refl ; false → refl })

  rd-rd : ∀ xtt xtf xft xff
    → rd (rd xtt xtf) (rd xft xff) ≡ rd xtt xff
  rd-rd xtt xtf xft xff =
    rd-wt _
    ∙ cong₂ rd
      (wt-rd _ _ _ ∙ wt-rd _ _ _ ∙ (sym $ wt-rd _ _ _))
      (wt-rd _ _ _ ∙ wt-rd _ _ _ ∙ (sym $ wt-rd _ _ _))
    ∙ (sym $ rd-wt _)

  rd-idempotent : ∀ x → rd x x ≡ x
  rd-idempotent x =
    rd-wt _
    ∙ cong₂ rd (wt-rd _ _ _) (wt-rd _ _ _)
    ∙ (sym $ rd-wt _)

-- Compare with Cubical.Algebra.State
module _ {X : Type ℓ} (B : S.StateAlg X) where
  private module B = S.StateAlg B
  fromStateAlg : StateAlg X
  fromStateAlg .Alg.⟨_⟩⟦_⟧op rdOp x = B.rd (x true) (x false)
  fromStateAlg .Alg.⟨_⟩⟦_⟧op (wtOp b) x = B.wt b (x tt)
  fromStateAlg .Alg.⟦_⟧eqn (wt-rdE true) ρ = B.wt-rd true (ρ true) (ρ false)
  fromStateAlg .Alg.⟦_⟧eqn (wt-rdE false) ρ = B.wt-rd false (ρ true) (ρ false)
  fromStateAlg .Alg.⟦_⟧eqn rd-wtE ρ = B.rd-wt (ρ tt)
  fromStateAlg .Alg.⟦_⟧eqn (wt-wtE b1 b2) ρ = B.wt-wt b1 b2 (ρ tt)

module _ {X : Type ℓ} (B : StateAlg X) where
  private module B = StateAlgNotation B
  toStateAlg : S.StateAlg X
  toStateAlg .S.StateAlg.rd = B.rd
  toStateAlg .S.StateAlg.wt = B.wt
  toStateAlg .S.StateAlg.wt-rd = B.wt-rd
  toStateAlg .S.StateAlg.rd-wt = B.rd-wt
  toStateAlg .S.StateAlg.wt-wt = B.wt-wt

-- S.StateAlg -> StateAlg -> S.StateAlg
module _ {X : Type ℓ} (B : S.StateAlg X) where
  private
    module B = S.StateAlg B
    module TB = S.StateAlg (toStateAlg (fromStateAlg B))

  to-from-rd : TB.rd ≡ B.rd
  to-from-rd = refl

  to-from-wt : TB.wt ≡ B.wt
  to-from-wt = refl

  to-from-wt-wt : TB.wt-wt ≡ B.wt-wt
  to-from-wt-wt = refl

  to-from-wt-rd : ∀ b xt xf → TB.wt-rd b xt xf ≡ B.wt-rd b xt xf
  to-from-wt-rd true xt xf = refl
  to-from-wt-rd false xt xf = refl

-- StateAlg -> S.StateAlg -> StateAlg
module _ {X : Type ℓ} (B : StateAlg X) where
  private
    module B = Alg B
    module FTB = Alg (fromStateAlg (toStateAlg B))

  from-to-wtOp : ∀ b (x : Unit → X)
    → FTB.⟨ wtOp b ⟩⟦ x ⟧op ≡ B.⟨ wtOp b ⟩⟦ x ⟧op
  from-to-wtOp b x = refl

  from-to-rdOp : ∀ (x : Bool → X)
    → FTB.⟨ rdOp ⟩⟦ x ⟧op ≡ B.⟨ rdOp ⟩⟦ x ⟧op
  from-to-rdOp x =
    cong (λ y → B.⟨ rdOp ⟩⟦ y ⟧op)
      (funExt {f = λ c → if c then x true else x false} {g = x}
        λ { true → refl ; false → refl })

StateAlgᴰ : {X : Type ℓ} → StateAlg X → (X → Type ℓᴰ) → Type _
StateAlgᴰ = Algᴰ StateTheory

module StateAlgᴰNotation {X : Type ℓ} {B : StateAlg X} {Xᴰ : X → Type ℓᴰ}
  (Bᴰ : StateAlgᴰ B Xᴰ) where
  private module B = StateAlgNotation B
  open Algᴰ Bᴰ public using (_P≡[_]_)
  private module Bᴰ = Algᴰ Bᴰ

  brs : ∀ {xt xf} → Xᴰ xt → Xᴰ xf → (c : Bool) → Xᴰ (if c then xt else xf)
  brs {xt} {xf} xtᴰ xfᴰ =
    Bool.elim {A = λ c → Xᴰ (if c then xt else xf)} xtᴰ xfᴰ

  rdᴰ' : ∀ {g : Bool → X} → ((c : Bool) → Xᴰ (g c)) → Xᴰ (B.rd' g)
  rdᴰ' = Bᴰ.⟨ rdOp ⟩⟦_⟧opᴰ

  rdᴰ : ∀ {xt xf} → Xᴰ xt → Xᴰ xf → Xᴰ (B.rd xt xf)
  rdᴰ xtᴰ xfᴰ = rdᴰ' (brs xtᴰ xfᴰ)

  wtᴰ : ∀ {x} b → Xᴰ x → Xᴰ (B.wt b x)
  wtᴰ b xᴰ = Bᴰ.⟨ wtOp b ⟩⟦ (λ _ → xᴰ) ⟧opᴰ

  wt-rdᴰ : ∀ b xt xf (xtᴰ : Xᴰ xt) (xfᴰ : Xᴰ xf)
    → wtᴰ b (rdᴰ xtᴰ xfᴰ) P≡[ B.wt-rd b xt xf ] wtᴰ b (brs xtᴰ xfᴰ b)
  wt-rdᴰ b xt xf xtᴰ xfᴰ = Bᴰ.⟦ wt-rdE b ⟧eqnᴰ (brs xtᴰ xfᴰ)

  wt-wtᴰ : ∀ b b' x (xᴰ : Xᴰ x)
    → wtᴰ b (wtᴰ b' xᴰ) P≡[ B.wt-wt b b' x ] wtᴰ b' xᴰ
  wt-wtᴰ b b' x xᴰ = Bᴰ.⟦ wt-wtE b b' ⟧eqnᴰ (λ _ → xᴰ)

  rd-wtᴰ' : ∀ x (xᴰ : Xᴰ x) → xᴰ P≡[ B.rd-wt' x ] rdᴰ' (λ c → wtᴰ c xᴰ)
  rd-wtᴰ' x xᴰ = Bᴰ.⟦ rd-wtE ⟧eqnᴰ (λ _ → xᴰ)
