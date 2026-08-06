-- Models of a *many-sorted* algebraic theory *internal* to the
-- presheaf category, and the theorem that a model in presheaves is the
-- same thing as a presheaf of models.
--
-- This is the sorted analogue of `Theory.Presheaf.Internal`.  The one
-- structural difference is the shape of the power an operation comes
-- out of: an operation's arguments sit at *different* sorts, so the
-- plain power `P ^Psh A` is replaced by the *dependent* power
-- `ΠPsh P as` of a sorted family of presheaves along a sorting
-- `as : A → S`.  It is still computed pointwise, which is the whole
-- content of the theorem.
module Cubical.Algebra.Theory.Sorted.Presheaf.Internal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base

open import Cubical.Algebra.Theory.Sorted
open import Cubical.Algebra.Theory.Sorted.Presheaf.Base

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓA ℓX ℓY ℓC ℓC' : Level

open Functor
open Iso
open PshHomStrict
open SortedSig
open SortedEqns

-- The dependent power of a sorted family of presheaves along a
-- sorting `as : A → S`, computed pointwise.  For `S = Unit` this is
-- the plain power `P ^Psh A` of `Theory.Presheaf.Internal`.
module _ {C : Category ℓC ℓC'} {S : Type ℓS} where
  private module C = Category C

  ΠPsh : (P : S → Presheaf C ℓX) {A : Type ℓA} (as : A → S)
    → Presheaf C (ℓ-max ℓX ℓA)
  ΠPsh P as .F-ob c =
    ((a : _) → ⟨ P (as a) ⟅ c ⟆ ⟩) , isSetΠ (λ a → str (P (as a) ⟅ c ⟆))
  ΠPsh P as .F-hom f x a = P (as a) .F-hom f (x a)
  ΠPsh P as .F-id i x a = P (as a) .F-id i (x a)
  ΠPsh P as .F-seq f g i x a = P (as a) .F-seq f g i (x a)

  module _ {P : S → Presheaf C ℓX} {A : Type ℓA} {as : A → S} where
    πPshˢ : (a : A) → PshHomStrict (ΠPsh P as) (P (as a))
    πPshˢ a .N-ob c x = x a
    πPshˢ a .N-hom c c' f x' x e = funExt⁻ e a

    module _ {Q : Presheaf C ℓY} where
      tuplePshˢ : ((a : A) → PshHomStrict Q (P (as a)))
        → PshHomStrict Q (ΠPsh P as)
      tuplePshˢ fam .N-ob c q a = fam a .N-ob c q
      tuplePshˢ fam .N-hom c c' f q' q e =
        funExt (λ a → fam a .N-hom c c' f q' q e)

      -- `ΠPsh P as` is the A-indexed product of the `P (as a)`.  As in
      -- the single-sorted case this is stated for hom-sets between
      -- presheaves of *different* levels: `ΠPsh P as` is an object of
      -- `PRESHEAF C ℓX` only when ℓA ≤ ℓX, but `PshHomStrict` is
      -- level-heterogeneous, so arbitrary arities need no lifting.
      ΠPshUP : Iso (PshHomStrict Q (ΠPsh P as))
                   ((a : A) → PshHomStrict Q (P (as a)))
      ΠPshUP .fun β a = β ⋆PshHomStrict πPshˢ a
      ΠPshUP .inv = tuplePshˢ
      ΠPshUP .sec fam = funExt (λ a → makePshHomStrictPath refl)
      ΠPshUP .ret β = makePshHomStrictPath refl

  -- The functorial action of the dependent power: postcomposition
  -- with a sortwise family of morphisms.
  ΠPshHom : {P : S → Presheaf C ℓX} {Q : S → Presheaf C ℓY}
    (α : (s : S) → PshHomStrict (P s) (Q s))
    {A : Type ℓA} (as : A → S)
    → PshHomStrict (ΠPsh P as) (ΠPsh Q as)
  ΠPshHom α as = tuplePshˢ (λ a → πPshˢ a ⋆PshHomStrict α (as a))

-- An algebra internal to `FAMPSH S C`: the operations are morphisms
-- out of the dependent powers along the argument sortings, landing in
-- the presheaf at the result sort, and the equations are equations
-- between the induced morphisms out of the power by the variables.
module _ {C : Category ℓC ℓC'} {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' ℓv) where
  private module C = Category C

  module _ (P : S → Presheaf C ℓX) where

    IntAlgOpsˢ : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓ ℓ') ℓX))
    IntAlgOpsˢ = (o : σ .ops)
      → PshHomStrict (ΠPsh P (σ .sortOf o)) (P (σ .resultSort o))

    module _ (α : IntAlgOpsˢ) where
      -- A term in V variables, sorted by `vs`, denotes a morphism out
      -- of the dependent power along `vs`.
      tmHomˢ : {V : Type ℓv} {vs : V → S} {s : S}
        → Tm σ V vs s → PshHomStrict (ΠPsh P vs) (P s)
      tmHomˢ (var v) = πPshˢ v
      tmHomˢ (node o ts) =
        tuplePshˢ (λ a → tmHomˢ (ts a)) ⋆PshHomStrict α o

      -- The pointwise operations underlying the internal ones.
      opAtˢ : (c : C.ob) → Ops {σ = σ} (λ s → ⟨ P s ⟅ c ⟆ ⟩)
      opAtˢ c o x = α o .N-ob c x

      -- Internal denotation is pointwise the set-level denotation.
      tmHomAtˢ : {V : Type ℓv} {vs : V → S} {s : S} (M : Tm σ V vs s)
        (c : C.ob) (ρ : (v : V) → ⟨ P (vs v) ⟅ c ⟆ ⟩)
        → tmHomˢ M .N-ob c ρ ≡ TmRec (λ s → ⟨ P s ⟅ c ⟆ ⟩) (opAtˢ c) ρ M
      tmHomAtˢ (var v) c ρ = refl
      tmHomAtˢ (node o ts) c ρ =
        cong (α o .N-ob c) (funExt (λ a → tmHomAtˢ (ts a) c ρ))

    record IntAlgˢ : Type (ℓ-max (ℓ-max ℓC ℓC')
                            (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max (ℓ-max ℓ'' ℓv) ℓX)))
      where
      field
        opᴵ : IntAlgOpsˢ
      ⟦_⟧Tmᴵ : {V : Type ℓv} {vs : V → S} {s : S}
        → Tm σ V vs s → PshHomStrict (ΠPsh P vs) (P s)
      ⟦_⟧Tmᴵ = tmHomˢ opᴵ
      field
        ⟦_⟧eqnᴵ : (e : σeq .eqns) → ⟦ σeq .lhs e ⟧Tmᴵ ≡ ⟦ σeq .rhs e ⟧Tmᴵ

    open IntAlgˢ
    open PshAlgˢ

    private
      isSetP : (c : C.ob) (s : S) → isSet ⟨ P s ⟅ c ⟆ ⟩
      isSetP c s = str (P s ⟅ c ⟆)

    -- A model in presheaves gives a presheaf of models: the pointwise
    -- algebras are the components of the operations, and the fact that
    -- restriction is a homomorphism is naturality.
    IntAlg→PshAlgˢ : IntAlgˢ → PshAlgˢ σeq P
    IntAlg→PshAlgˢ A .alg = opAtˢ (A .opᴵ)
    IntAlg→PshAlgˢ A .sat c e ρ =
      sym (tmHomAtˢ (A .opᴵ) (σeq .lhs e) c ρ)
      ∙ (λ i → A .⟦_⟧eqnᴵ e i .N-ob c ρ)
      ∙ tmHomAtˢ (A .opᴵ) (σeq .rhs e) c ρ
    IntAlg→PshAlgˢ A .restr {c} {c'} f o x y eq =
      cong (λ z → (P (σ .resultSort o) ⟪ f ⟫) z) eq
      ∙ A .opᴵ o .N-hom c c' f x _ refl

    -- ... and conversely.
    module _ (B : PshAlgˢ σeq P) where
      PshAlg→IntAlgOpsˢ : IntAlgOpsˢ
      PshAlg→IntAlgOpsˢ o .N-ob c x = B .alg c o x
      PshAlg→IntAlgOpsˢ o .N-hom c c' f x' x e =
        B .restr f o x' _ refl ∙ cong (λ z → B .alg c o z) e

      PshAlg→IntAlgˢ : IntAlgˢ
      PshAlg→IntAlgˢ .opᴵ = PshAlg→IntAlgOpsˢ
      PshAlg→IntAlgˢ .⟦_⟧eqnᴵ e = makePshHomStrictPath (funExt (λ c →
        funExt (λ ρ →
          tmHomAtˢ PshAlg→IntAlgOpsˢ (σeq .lhs e) c ρ
          ∙ B .sat c e ρ
          ∙ sym (tmHomAtˢ PshAlg→IntAlgOpsˢ (σeq .rhs e) c ρ))))

    -- Both notions are determined by their operations: `sat` is a path
    -- in a set, `restr` lands in a set and is forded, and `⟦_⟧eqnᴵ` is
    -- a path in `isSetPshHomStrict`.
    IntAlgˢ≡ : {A A' : IntAlgˢ} → A .opᴵ ≡ A' .opᴵ → A ≡ A'
    IntAlgˢ≡ p i .opᴵ = p i
    IntAlgˢ≡ {A} {A'} p i .⟦_⟧eqnᴵ =
      isProp→PathP
        (λ j → isPropΠ (λ e →
          isSetPshHomStrict (ΠPsh P (σeq .varSort e)) (P (σeq .eqnSort e))
            (tmHomˢ (p j) (σeq .lhs e)) (tmHomˢ (p j) (σeq .rhs e))))
        (A .⟦_⟧eqnᴵ) (A' .⟦_⟧eqnᴵ) i

    private
      -- The two remaining fields of `PshAlgˢ`, as families over the
      -- operations.  Spelling them out is what lets `isProp→PathP`
      -- see the motive; left as `_` the `isPropΠ`s do not solve.
      AlgTy : Type _
      AlgTy = (c : C.ob) → Ops {σ = σ} (λ s → ⟨ P s ⟅ c ⟆ ⟩)

      SatTy : AlgTy → Type _
      SatTy a = (c : C.ob) (e : σeq .eqns)
        (ρ : (v : σeq .vars e) → ⟨ P (σeq .varSort e v) ⟅ c ⟆ ⟩)
        → TmRec (λ s → ⟨ P s ⟅ c ⟆ ⟩) (a c) ρ (σeq .lhs e)
          ≡ TmRec (λ s → ⟨ P s ⟅ c ⟆ ⟩) (a c) ρ (σeq .rhs e)

      isPropSatTy : (a : AlgTy) → isProp (SatTy a)
      isPropSatTy a =
        isPropΠ3 (λ c e ρ → isSetP c (σeq .eqnSort e) _ _)

      RestrTy : AlgTy → Type _
      RestrTy a = {c c' : C.ob} (f : C [ c , c' ])
        → Homoˢ (λ s → P s ⟪ f ⟫) (a c') (a c)

      isPropRestrTy : (a : AlgTy) → isProp (RestrTy a)
      isPropRestrTy a =
        isPropImplicitΠ2 (λ c c' → isPropΠ (λ f →
          isPropΠ4 (λ o x y eq → isSetP c (σ .resultSort o) _ _)))

    PshAlgˢ≡ : {B B' : PshAlgˢ σeq P} → B .alg ≡ B' .alg → B ≡ B'
    PshAlgˢ≡ p i .alg = p i
    PshAlgˢ≡ {B} {B'} p i .sat =
      isProp→PathP (λ j → isPropSatTy (p j)) (B .sat) (B' .sat) i
    PshAlgˢ≡ {B} {B'} p i .restr =
      isProp→PathP (λ j → isPropRestrTy (p j)) (B .restr) (B' .restr) i

    -- THE THEOREM: a many-sorted model in presheaves is a presheaf of
    -- many-sorted models.  Both round trips are the identity on the
    -- operation data; only the propositional fields move.
    IntAlgˢ≅PshAlgˢ : Iso IntAlgˢ (PshAlgˢ σeq P)
    IntAlgˢ≅PshAlgˢ .fun = IntAlg→PshAlgˢ
    IntAlgˢ≅PshAlgˢ .inv = PshAlg→IntAlgˢ
    IntAlgˢ≅PshAlgˢ .sec B = PshAlgˢ≡ refl
    IntAlgˢ≅PshAlgˢ .ret A =
      IntAlgˢ≡ (funExt (λ o → makePshHomStrictPath refl))

  -- Homomorphisms: an internal homomorphism is a sortwise family of
  -- presheaf morphisms making the operation squares commute, and that
  -- is the same thing as a family of homomorphisms of the pointwise
  -- sorted algebras.
  module _ {P Q : S → Presheaf C ℓX}
    (α : (s : S) → PshHomStrict (P s) (Q s))
    (A : IntAlgˢ P) (D : IntAlgˢ Q) where
    open IntAlgˢ

    IntAlgHomoˢ : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓ ℓ') ℓX))
    IntAlgHomoˢ = (o : σ .ops) →
      ΠPshHom α (σ .sortOf o) ⋆PshHomStrict D .opᴵ o
      ≡ A .opᴵ o ⋆PshHomStrict α (σ .resultSort o)

    isPropIntAlgHomoˢ : isProp IntAlgHomoˢ
    isPropIntAlgHomoˢ = isPropΠ (λ o →
      isSetPshHomStrict (ΠPsh P (σ .sortOf o)) (Q (σ .resultSort o)) _ _)

    isPropPshAlgHomoˢ :
      isProp (PshAlgHomoˢ σeq α (IntAlg→PshAlgˢ P A) (IntAlg→PshAlgˢ Q D))
    isPropPshAlgHomoˢ = isPropΠ (λ c → isPropΠ4 (λ o x y eq →
      str (Q (σ .resultSort o) ⟅ c ⟆) _ _))

    IntAlgHomoˢ→PshAlgHomoˢ : IntAlgHomoˢ
      → PshAlgHomoˢ σeq α (IntAlg→PshAlgˢ P A) (IntAlg→PshAlgˢ Q D)
    IntAlgHomoˢ→PshAlgHomoˢ ϕ c o x y eq =
      cong (α (σ .resultSort o) .N-ob c) eq ∙ sym (λ i → ϕ o i .N-ob c x)

    PshAlgHomoˢ→IntAlgHomoˢ :
      PshAlgHomoˢ σeq α (IntAlg→PshAlgˢ P A) (IntAlg→PshAlgˢ Q D)
      → IntAlgHomoˢ
    PshAlgHomoˢ→IntAlgHomoˢ ψ o = makePshHomStrictPath (funExt (λ c →
      funExt (λ x → sym (ψ c o x _ refl))))

    IntAlgHomoˢ≅PshAlgHomoˢ : Iso IntAlgHomoˢ
      (PshAlgHomoˢ σeq α (IntAlg→PshAlgˢ P A) (IntAlg→PshAlgˢ Q D))
    IntAlgHomoˢ≅PshAlgHomoˢ .fun = IntAlgHomoˢ→PshAlgHomoˢ
    IntAlgHomoˢ≅PshAlgHomoˢ .inv = PshAlgHomoˢ→IntAlgHomoˢ
    IntAlgHomoˢ≅PshAlgHomoˢ .sec ψ = isPropPshAlgHomoˢ _ ψ
    IntAlgHomoˢ≅PshAlgHomoˢ .ret ϕ = isPropIntAlgHomoˢ _ ϕ
