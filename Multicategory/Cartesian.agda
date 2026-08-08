{-

  A CARTESIAN multicategory, algebraically: operations and equations,
  no universal structure anywhere — the same kind of definition as a
  category or a displayed category.

  The one change from Multicategory.Base is that composition does NOT
  form Σ I J.  A substitution assigns to every position of Γ a
  multimorphism out of a COMMON arity J, so the composite has arity J
  and every law states homogeneously.  Nothing has to be coherent about
  arities because no arity is ever built.

  SET is then strict: ⋆Var, ⋆Id and ⋆Assoc are all refl, at every
  arity, by η for functions.

  Cartesian is meant literally: the positions of Γ share the arity J,
  so reindexing them along an arbitrary function is derivable (see
  reindex below) — φ non-injective is contraction, non-surjective is
  weakening, a permutation is exchange.  A *clone* is the one-object
  case (nLab: abstract clone = cartesian operad = one-object cartesian
  multicategory), and Endₘ below is one: the endomorphism clone of a
  set.  Since arities here are arbitrary types rather than finite ones,
  that one-object case is a Kleisli triple — var is return, _⋆_ is
  bind, the three laws are the monad laws, and Endₘ X is the
  continuation monad at answer type X.  That is also the reason SET is
  strict: those laws are η for functions.

  A linear multicategory has to concatenate the sub-arities, and no
  encoding of concatenation is strict — see Multicategory.Nat.

-}
module Multicategory.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.FinData

private
  variable
    ℓM ℓM' ℓI ℓJ ℓK : Level

-- NB: the arities range over a FIXED level ℓI.  Quantifying over all
-- levels would push the record into Typeω, and then no inductively
-- defined syntax could be an instance: an inductive family cannot have
-- a constructor relating two different level instantiations.
record CartesianMulticategory (ℓI ℓM ℓM' : Level)
    : Type (ℓ-suc (ℓ-max ℓI (ℓ-max ℓM ℓM'))) where
  field
    ob : Type ℓM
    MHom⟨_⟩[_,_] : (I : Type ℓI) → (I → ob) → ob → Type ℓM'

  MHom[_,_] : {I : Type ℓI} → (I → ob) → ob → Type ℓM'
  MHom[_,_] {I = I} = MHom⟨ I ⟩[_,_]

  Ctx : Type ℓI → Type (ℓ-max ℓM ℓI)
  Ctx I = I → ob

  field
    -- the multimorphism that projects the i-th position.  At a
    -- singleton arity this is the identity.
    var : {I : Type ℓI} {Γ : Ctx I} (i : I) → MHom[ Γ , Γ i ]

    -- substitution: every position of Γ is filled by a multimorphism
    -- out of the same arity J
    _⋆_ : {I J : Type ℓI} {Γ : Ctx I} {Δ : Ctx J} {A : ob}
      → MHom[ Γ , A ]
      → ((i : I) → MHom[ Δ , Γ i ])
      → MHom[ Δ , A ]

    -- THE LAWS.  All three are homogeneous.
    ⋆Var : {I J : Type ℓI} {Γ : Ctx I} {Δ : Ctx J}
      (i : I) (f : (i : I) → MHom[ Δ , Γ i ])
      → var i ⋆ f ≡ f i
    ⋆Id : {I : Type ℓI} {Γ : Ctx I} {A : ob}
      (M : MHom[ Γ , A ])
      → M ⋆ var ≡ M
    ⋆Assoc : {I J K : Type ℓI}
      {Γ : Ctx I} {Δ : Ctx J} {Θ : Ctx K} {A : ob}
      (M : MHom[ Γ , A ])
      (f : (i : I) → MHom[ Δ , Γ i ])
      (g : (j : J) → MHom[ Θ , Δ j ])
      → (M ⋆ f) ⋆ g ≡ M ⋆ (λ i → f i ⋆ g)

    isSetMHom : ∀ {I : Type ℓI} {Γ : Ctx I} {A} → isSet (MHom⟨ I ⟩[ Γ , A ])

  -- the identity is var at a singleton arity
  id : ∀ {A} → MHom⟨ Unit* ⟩[ (λ _ → A) , A ]
  id = var tt*

  -- THE CARTESIAN STRUCTURE, derived: positions are reindexed along an
  -- arbitrary function.  φ non-injective is contraction, φ
  -- non-surjective is weakening, a permutation is exchange.
  reindex : {I J : Type ℓI} {Δ : Ctx J} {A : ob}
    (φ : I → J) → MHom[ Δ ∘ φ , A ] → MHom[ Δ , A ]
  reindex φ M = M ⋆ (λ i → var (φ i))

  reindex-id : {I : Type ℓI} {Γ : Ctx I} {A : ob} (M : MHom[ Γ , A ])
    → reindex (idfun I) M ≡ M
  reindex-id = ⋆Id

  reindex-seq : {I J K : Type ℓI}
    {Θ : Ctx K} {A : ob} (φ : I → J) (ψ : J → K)
    (M : MHom[ (λ i → Θ (ψ (φ i))) , A ])
    → reindex {Δ = Θ} ψ (reindex {Δ = λ j → Θ (ψ j)} φ M)
      ≡ reindex {Δ = Θ} (λ i → ψ (φ i)) M
  reindex-seq φ ψ M =
    ⋆Assoc M _ _ ∙ cong (M ⋆_) (funExt λ i → ⋆Var (φ i) _)

-- SET is strict: every law is refl, at every arity.  (The fields are
-- written qualified so the names stay free for the module below.)

SETₘ : ∀ {ℓI ℓ} → CartesianMulticategory ℓI (ℓ-suc ℓ) (ℓ-max ℓI ℓ)
SETₘ .CartesianMulticategory.ob = hSet _
SETₘ .CartesianMulticategory.MHom⟨_⟩[_,_] I Γ A = ((i : I) → ⟨ Γ i ⟩) → ⟨ A ⟩
SETₘ .CartesianMulticategory.var i γ = γ i
SETₘ .CartesianMulticategory._⋆_ M f δ = M (λ i → f i δ)
-- THE LAWS
SETₘ .CartesianMulticategory.⋆Var i f = refl
SETₘ .CartesianMulticategory.⋆Id M = refl
SETₘ .CartesianMulticategory.⋆Assoc M f g = refl
SETₘ .CartesianMulticategory.isSetMHom {A = A} = isSet→ (str A)

module Computation where
  open CartesianMulticategory (SETₘ {ℓ-zero} {ℓ-zero})

  ℕs : hSet ℓ-zero
  ℕs = ℕ , isSetℕ

  Γ₂ : Ctx Bool
  Γ₂ _ = ℕs

  Γ₃ : Ctx (Fin 3)
  Γ₃ _ = ℕs

  -- a binary multimorphism: arity Bool
  plus : MHom⟨ Bool ⟩[ Γ₂ , ℕs ]
  plus γ = γ true + γ false

  -- substitution at these arities, with the implicits pinned once
  _⊙_ : MHom⟨ Bool ⟩[ Γ₂ , ℕs ]
    → ((b : Bool) → MHom⟨ Fin 3 ⟩[ Γ₃ , ℕs ])
    → MHom⟨ Fin 3 ⟩[ Γ₃ , ℕs ]
  M ⊙ f = _⋆_ {I = Bool} {J = Fin 3} {Γ = Γ₂} {Δ = Γ₃} {A = ℕs} M f

  -- and a ternary one, built by substitution.  It computes.
  -- (The pins are green slime from SET's MHom being a function type,
  -- not a coherence cost.)
  vr : Fin 3 → MHom⟨ Fin 3 ⟩[ Γ₃ , ℕs ]
  vr i = var {Γ = Γ₃} i

  sum₃ : MHom⟨ Fin 3 ⟩[ Γ₃ , ℕs ]
  sum₃ = plus ⊙ f
    where
    g : (b : Bool) → MHom⟨ Fin 3 ⟩[ Γ₃ , ℕs ]
    g true = vr (suc zero)
    g false = vr (suc (suc zero))

    f : (b : Bool) → MHom⟨ Fin 3 ⟩[ Γ₃ , ℕs ]
    f true = vr zero
    f false = plus ⊙ g

  _ : sum₃ (λ i → suc (toℕ i)) ≡ 6
  _ = refl

-- the one-object case: the endomorphism clone of a set.  Same laws,
-- same proofs — a clone is a cartesian multicategory that happens to
-- have one object, and with type arities it is a Kleisli triple.
Endₘ : ∀ {ℓI ℓ} → hSet ℓ → CartesianMulticategory ℓI ℓ-zero (ℓ-max ℓI ℓ)
Endₘ X .CartesianMulticategory.ob = Unit
Endₘ X .CartesianMulticategory.MHom⟨_⟩[_,_] I _ _ = (I → ⟨ X ⟩) → ⟨ X ⟩
Endₘ X .CartesianMulticategory.var i γ = γ i
Endₘ X .CartesianMulticategory._⋆_ M f δ = M (λ i → f i δ)
Endₘ X .CartesianMulticategory.⋆Var i f = refl
Endₘ X .CartesianMulticategory.⋆Id M = refl
Endₘ X .CartesianMulticategory.⋆Assoc M f g = refl
Endₘ X .CartesianMulticategory.isSetMHom = isSet→ (str X)
