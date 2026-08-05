-- Algebras *internal* to the presheaf category, and the theorem that a
-- model in presheaves is the same thing as a presheaf of models.
module Cubical.Algebra.Theory.Presheaf.Internal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Presheaf.Base

private
  variable
    ℓ ℓ' ℓ'' ℓv ℓA ℓX ℓY ℓC ℓC' : Level

open Functor
open Iso
open PshHomStrict

-- Powers of a presheaf by an arbitrary type, computed pointwise.
module _ {C : Category ℓC ℓC'} where
  _^Psh_ : Presheaf C ℓX → (A : Type ℓA) → Presheaf C (ℓ-max ℓX ℓA)
  (P ^Psh A) .F-ob c = (A → ⟨ P ⟅ c ⟆ ⟩) , isSet→ (str (P ⟅ c ⟆))
  (P ^Psh A) .F-hom f x a = P .F-hom f (x a)
  (P ^Psh A) .F-id i x a = P .F-id i (x a)
  (P ^Psh A) .F-seq f g i x a = P .F-seq f g i (x a)

  infixl 6 _^Psh_

  module _ {P : Presheaf C ℓX} {A : Type ℓA} where
    πPsh : (a : A) → PshHomStrict (P ^Psh A) P
    πPsh a .N-ob c x = x a
    πPsh a .N-hom c c' f x' x e = funExt⁻ e a

    module _ {Q : Presheaf C ℓY} where
      tuplePsh : ((a : A) → PshHomStrict Q P) → PshHomStrict Q (P ^Psh A)
      tuplePsh fam .N-ob c q a = fam a .N-ob c q
      tuplePsh fam .N-hom c c' f q' q e =
        funExt (λ a → fam a .N-hom c c' f q' q e)

      -- `P ^Psh A` is the A-indexed product of copies of P.  Note this
      -- is stated for hom-sets between presheaves of *different*
      -- levels: `P ^Psh A` is not an object of `PRESHEAF C ℓX` unless
      -- ℓA ≤ ℓX, but `PshHomStrict` is level-heterogeneous, so nothing
      -- needs lifting.
      ^PshUP : Iso (PshHomStrict Q (P ^Psh A)) ((a : A) → PshHomStrict Q P)
      ^PshUP .fun β a = β ⋆PshHomStrict πPsh a
      ^PshUP .inv = tuplePsh
      ^PshUP .sec fam = funExt (λ a → makePshHomStrictPath refl)
      ^PshUP .ret β = makePshHomStrictPath refl

  -- The functorial action of the power, i.e. postcomposition.
  _^PshHom_ : {P : Presheaf C ℓX} {Q : Presheaf C ℓY}
    (α : PshHomStrict P Q) (A : Type ℓA)
    → PshHomStrict (P ^Psh A) (Q ^Psh A)
  α ^PshHom A = tuplePsh (λ a → πPsh a ⋆PshHomStrict α)

  infixl 6 _^PshHom_

-- An algebra internal to PRESHEAF C: the operations are morphisms out
-- of the powers, and the equations are equations between the induced
-- morphisms out of the power by the variables.
module _ {C : Category ℓC ℓC'} {σ : AlgTheorySig ℓ ℓ'}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) where
  private module C = Category C
  open AlgTheoryEqns σeq

  -- An algebra is determined by its operations: the equations are
  -- paths in a set, hence propositional.
  Alg≡ : {X : Type ℓX} → isSet X → {B B' : Alg σeq X}
    → B .Alg.⟨_⟩⟦_⟧op ≡ B' .Alg.⟨_⟩⟦_⟧op → B ≡ B'
  Alg≡ isSetX p i .Alg.⟨_⟩⟦_⟧op = p i
  Alg≡ isSetX {B} {B'} p i .Alg.⟦_⟧eqn =
    isProp→PathP
      (λ j → isPropΠ2 (λ eqn ρ →
        isSetX (TmRec (p j) ρ (lhs eqn)) (TmRec (p j) ρ (rhs eqn))))
      (B .Alg.⟦_⟧eqn) (B' .Alg.⟦_⟧eqn) i

  module _ (P : Presheaf C ℓX) where
    private module P = PresheafNotation P

    IntAlgOps : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓ ℓ') ℓX))
    IntAlgOps = (op : ops) → PshHomStrict (P ^Psh arities op) P

    module _ (α : IntAlgOps) where
      -- A term in V variables denotes a morphism out of the V-power.
      tmHom : {V : Type ℓv} → Tm σ V → PshHomStrict (P ^Psh V) P
      tmHom (var v) = πPsh v
      tmHom (node op ts) = tuplePsh (λ a → tmHom (ts a)) ⋆PshHomStrict α op

      -- The pointwise operations underlying the internal ones.
      opAt : (c : C.ob) (op : ops) → (arities op → P.p[ c ]) → P.p[ c ]
      opAt c op x = α op .N-ob c x

      -- Internal denotation is pointwise the set-level denotation.
      tmHomAt : {V : Type ℓv} (M : Tm σ V) (c : C.ob) (ρ : V → P.p[ c ])
        → tmHom M .N-ob c ρ ≡ TmRec (opAt c) ρ M
      tmHomAt (var v) c ρ = refl
      tmHomAt (node op ts) c ρ =
        cong (α op .N-ob c) (funExt (λ a → tmHomAt (ts a) c ρ))

    record IntAlg : Type (ℓ-max (ℓ-max ℓC ℓC')
                           (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max (ℓ-max ℓ'' ℓv) ℓX)))
      where
      field
        opᴵ : IntAlgOps
      ⟦_⟧Tmᴵ : {V : Type ℓv} → Tm σ V → PshHomStrict (P ^Psh V) P
      ⟦_⟧Tmᴵ = tmHom opᴵ
      field
        ⟦_⟧eqnᴵ : (eqn : eqns) → ⟦ lhs eqn ⟧Tmᴵ ≡ ⟦ rhs eqn ⟧Tmᴵ

    open IntAlg
    open PshAlg
    open Alg
    open Homo

    -- A model in presheaves gives a presheaf of models: the pointwise
    -- algebras are the components of the operations, and the fact that
    -- restriction is a homomorphism is naturality.
    IntAlg→PshAlg : IntAlg → PshAlg σeq P
    IntAlg→PshAlg A .alg c .⟨_⟩⟦_⟧op = opAt (A .opᴵ) c
    IntAlg→PshAlg A .alg c .⟦_⟧eqn eqn ρ =
      sym (tmHomAt (A .opᴵ) (lhs eqn) c ρ)
      ∙ (λ i → A .⟦_⟧eqnᴵ eqn i .N-ob c ρ)
      ∙ tmHomAt (A .opᴵ) (rhs eqn) c ρ
    IntAlg→PshAlg A .restr {c} {c'} f .op-hom op x y eq =
      cong (P._⋆_ f) eq ∙ A .opᴵ op .N-hom c c' f x _ refl

    -- ... and conversely.
    module _ (B : PshAlg σeq P) where
      PshAlg→IntAlgOps : IntAlgOps
      PshAlg→IntAlgOps op .N-ob c x = B .alg c .⟨_⟩⟦_⟧op op x
      PshAlg→IntAlgOps op .N-hom c c' f x' x e =
        B .restr f .op-hom op x' _ refl
        ∙ cong (λ z → B .alg c .⟨_⟩⟦_⟧op op z) e

      PshAlg→IntAlg : IntAlg
      PshAlg→IntAlg .opᴵ = PshAlg→IntAlgOps
      PshAlg→IntAlg .⟦_⟧eqnᴵ eqn = makePshHomStrictPath (funExt (λ c →
        funExt (λ ρ →
          tmHomAt PshAlg→IntAlgOps (lhs eqn) c ρ
          ∙ B .alg c .⟦_⟧eqn eqn ρ
          ∙ sym (tmHomAt PshAlg→IntAlgOps (rhs eqn) c ρ))))

    -- Both notions are determined by their operations: the equations
    -- are paths in a set (`P.isSetPsh`, resp. `isSetPshHomStrict`) and
    -- `Homo` is propositional.
    IntAlg≡ : {A A' : IntAlg} → A .opᴵ ≡ A' .opᴵ → A ≡ A'
    IntAlg≡ p i .opᴵ = p i
    IntAlg≡ {A} {A'} p i .⟦_⟧eqnᴵ =
      isProp→PathP
        (λ j → isPropΠ (λ eqn →
          isSetPshHomStrict (P ^Psh vars eqn) P
            (tmHom (p j) (lhs eqn)) (tmHom (p j) (rhs eqn))))
        (A .⟦_⟧eqnᴵ) (A' .⟦_⟧eqnᴵ) i

    PshAlg≡ : {B B' : PshAlg σeq P} → B .alg ≡ B' .alg → B ≡ B'
    PshAlg≡ p i .alg = p i
    PshAlg≡ {B} {B'} p i .restr =
      isProp→PathP
        (λ j → isPropImplicitΠ2 (λ c c' → isPropΠ (λ f →
          isPropHomo σeq {B = p j c'} {C = p j c} {f = P._⋆_ f}
            P.isSetPsh)))
        (B .restr) (B' .restr) i

    -- THE THEOREM: a model in presheaves is a presheaf of models.
    IntAlg≅PshAlg : Iso IntAlg (PshAlg σeq P)
    IntAlg≅PshAlg .fun = IntAlg→PshAlg
    IntAlg≅PshAlg .inv = PshAlg→IntAlg
    IntAlg≅PshAlg .sec B = PshAlg≡ (funExt (λ c → Alg≡ P.isSetPsh refl))
    IntAlg≅PshAlg .ret A =
      IntAlg≡ (funExt (λ op → makePshHomStrictPath refl))

  -- Homomorphisms: an internal homomorphism is a morphism of presheaves
  -- making the operation squares commute, and that is the same thing as
  -- a family of homomorphisms of the pointwise algebras.
  module _ {P : Presheaf C ℓX} {Q : Presheaf C ℓY}
    (α : PshHomStrict P Q) (A : IntAlg P) (D : IntAlg Q) where
    private module Q = PresheafNotation Q
    open IntAlg
    open Homo

    IntAlgHomo :
      Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓX ℓY)))
    IntAlgHomo = (op : ops) →
      (α ^PshHom arities op) ⋆PshHomStrict D .opᴵ op
      ≡ A .opᴵ op ⋆PshHomStrict α

    isPropIntAlgHomo : isProp IntAlgHomo
    isPropIntAlgHomo = isPropΠ (λ op →
      isSetPshHomStrict (P ^Psh arities op) Q _ _)

    IntAlgHomo→PshAlgHomo : IntAlgHomo
      → PshAlgHomo σeq α (IntAlg→PshAlg P A) (IntAlg→PshAlg Q D)
    IntAlgHomo→PshAlgHomo ϕ c .op-hom op x y eq =
      cong (α .N-ob c) eq ∙ sym (λ i → ϕ op i .N-ob c x)

    PshAlgHomo→IntAlgHomo :
      PshAlgHomo σeq α (IntAlg→PshAlg P A) (IntAlg→PshAlg Q D)
      → IntAlgHomo
    PshAlgHomo→IntAlgHomo ψ op = makePshHomStrictPath (funExt (λ c →
      funExt (λ x → sym (ψ c .op-hom op x _ refl))))

    IntAlgHomo≅PshAlgHomo : Iso IntAlgHomo
      (PshAlgHomo σeq α (IntAlg→PshAlg P A) (IntAlg→PshAlg Q D))
    IntAlgHomo≅PshAlgHomo .fun = IntAlgHomo→PshAlgHomo
    IntAlgHomo≅PshAlgHomo .inv = PshAlgHomo→IntAlgHomo
    IntAlgHomo≅PshAlgHomo .sec ψ =
      isPropΠ (λ c → isPropHomo σeq Q.isSetPsh) _ ψ
    IntAlgHomo≅PshAlgHomo .ret ϕ = isPropIntAlgHomo _ ϕ
