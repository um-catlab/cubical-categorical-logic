-- Groups by generators and relations.
--
-- Nothing about `Presentation` was specific to rings, so the cyclic
-- group ⟨x | xⁿ = e⟩ is the same construction at the theory of groups,
-- and its classical universal property
--
--     Hom_Grp(Cₙ , G)  ≃  { g ∈ G : gⁿ = e }
--
-- is `UPPresented` composed with the bookkeeping that turns a term of
-- the theory into the n-fold product.
module Cubical.Algebra.Instances.PresentedGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Arity
open import Cubical.Algebra.Theory.Presentation
open import Cubical.Algebra.Instances.Group

private
  variable
    ℓ ℓX : Level

open AlgTheorySig
open Presentation

module _ {ℓ} where

  power : {V : Type ℓ} → ℕ → Tm (GroupSig ℓ) V → Tm (GroupSig ℓ) V
  power zero M = tmε
  power (suc n) M = tm· M (power n M)

  -- ⟨ x | xⁿ = e ⟩
  Cyclic : ℕ → Presentation (GroupSig ℓ) (A1 ℓ) ℓ-zero
  Cyclic n .rels = Unit
  Cyclic n .rl _ = power n (var u)
  Cyclic n .rr _ = tmε

  CyclicGroup : ℕ → Type _
  CyclicGroup n = Presented (Cyclic n) (GroupEqns ℓ)

  module _ {X : Type ℓX} (isSetX : isSet X) (B : Alg (GroupEqns ℓ) X) where
    open GroupNotation B
    private module B = Alg B

    pow : ℕ → X → X
    pow zero g = ε
    pow (suc n) g = g · pow n g

    private
      εEval : (ρ : A1 ℓ → X) → TmRec B.⟨_⟩⟦_⟧op ρ tmε ≡ ε
      εEval ρ = cong B.⟨ εOp ⟩⟦_⟧op (sel0η _)

      powEval : (n : ℕ) (ρ : A1 ℓ → X)
        → TmRec B.⟨_⟩⟦_⟧op ρ (power n (var u)) ≡ pow n (ρ u)
      powEval zero ρ = εEval ρ
      powEval (suc n) ρ =
        cong B.⟨ ·Op ⟩⟦_⟧op (sel2η _)
        ∙ cong (ρ u ·_) (powEval n ρ)

    -- the points of the presentation are the elements killed by n
    cyclicPoints : (n : ℕ)
      → Iso (Points (Cyclic n) (GroupEqns ℓ) isSetX B)
            (Σ[ g ∈ X ] pow n g ≡ ε)
    cyclicPoints n .Iso.fun (ρ , sol) =
      ρ u , sym (powEval n ρ) ∙ sol tt ∙ εEval ρ
    cyclicPoints n .Iso.inv (g , e) =
      sel1 g , λ _ → powEval n (sel1 g) ∙ e ∙ sym (εEval (sel1 g))
    cyclicPoints n .Iso.sec (g , e) =
      Σ≡Prop (λ _ → isSetX _ _) refl
    cyclicPoints n .Iso.ret (ρ , sol) =
      Σ≡Prop (λ _ → isPropΠ λ _ → isSetX _ _) (sym (sel1η ρ))

    -- the universal property of the cyclic group
    cyclicUP : (n : ℕ)
      → Iso (σHom (Cyclic n) (GroupEqns ℓ) isSetX B)
            (Σ[ g ∈ X ] pow n g ≡ ε)
    cyclicUP n = compIso
      (UPPresented (Cyclic n) (GroupEqns ℓ) isSetX B)
      (cyclicPoints n)
