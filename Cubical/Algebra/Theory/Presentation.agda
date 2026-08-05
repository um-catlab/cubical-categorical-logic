-- Presentations: generators and relations.
--
-- Adding equations to a theory imposes an identity on every model, which
-- is not what a relation between generators does: `x · x ≡ x` as an
-- equation is the theory of idempotent monoids, as a relation it only
-- constrains one chosen element.
--
-- Making the generators constants -- the `Pointed V` summand, which is
-- what makes `MOD` remember them -- collapses the difference: a relation
-- becomes an equation with *no* variables, so there is nothing left to
-- instantiate.  A presentation is then literally a theory, and the
-- presented model is its initial model.
module Cubical.Algebra.Theory.Presentation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥; ⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)

open import Cubical.Categories.Category

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Category
open import Cubical.Algebra.Theory.Theories
open import Cubical.Algebra.Theory.Constructions
open import Cubical.Algebra.Theory.Free.Constants
open import Cubical.Algebra.Theory.Free.Explicit
open import Cubical.Algebra.Theory.Free.Section hiding (gen)

private
  variable
    ℓ ℓ' ℓ'' ℓE ℓR ℓv ℓX : Level

open AlgTheorySig
open AlgTheoryEqns using (eqns; vars; lhs; rhs)

-- Extending a theory by more equations in the same signature.  Models of
-- the extension are the models of the original that satisfy them, and
-- `Homo` mentions only the signature, so `MOD` of the extension is a
-- full subcategory of `MOD` of the original.
module _ {σ : AlgTheorySig ℓ ℓ'} where

  Sat : {X : Type ℓX} (E : AlgTheoryEqns σ ℓE ℓv)
    (α : ∀ (op : σ .ops) → (σ .arities op → X) → X) → Type _
  Sat {X = X} E α = (e : E .eqns) (ρ : E .vars e → X)
    → TmRec α ρ (E .lhs e) ≡ TmRec α ρ (E .rhs e)

  isPropSat : {X : Type ℓX} {E : AlgTheoryEqns σ ℓE ℓv}
    {α : ∀ (op : σ .ops) → (σ .arities op → X) → X}
    → isSet X → isProp (Sat E α)
  isPropSat isSetX = isPropΠ2 λ _ _ → isSetX _ _

  _∪Eqns_ : AlgTheoryEqns σ ℓ'' ℓv → AlgTheoryEqns σ ℓE ℓv
    → AlgTheoryEqns σ (ℓ-max ℓ'' ℓE) ℓv
  (σeq ∪Eqns E) .eqns = σeq .eqns ⊎ E .eqns
  (σeq ∪Eqns E) .vars (inl e) = σeq .vars e
  (σeq ∪Eqns E) .vars (inr e) = E .vars e
  (σeq ∪Eqns E) .lhs (inl e) = σeq .lhs e
  (σeq ∪Eqns E) .lhs (inr e) = E .lhs e
  (σeq ∪Eqns E) .rhs (inl e) = σeq .rhs e
  (σeq ∪Eqns E) .rhs (inr e) = E .rhs e

  module _ (σeq : AlgTheoryEqns σ ℓ'' ℓv) (E : AlgTheoryEqns σ ℓE ℓv)
    {X : Type ℓX} where

    Alg∪ : Alg (σeq ∪Eqns E) X → Alg σeq X
    Alg∪ B .Alg.⟨_⟩⟦_⟧op = Alg.⟨_⟩⟦_⟧op B
    Alg∪ B .Alg.⟦_⟧eqn e = Alg.⟦_⟧eqn B (inl e)

    sat∪ : (B : Alg (σeq ∪Eqns E) X) → Sat E (Alg.⟨_⟩⟦_⟧op B)
    sat∪ B e = Alg.⟦_⟧eqn B (inr e)

    mk∪ : (B : Alg σeq X) → Sat E (Alg.⟨_⟩⟦_⟧op B) → Alg (σeq ∪Eqns E) X
    mk∪ B _ .Alg.⟨_⟩⟦_⟧op = Alg.⟨_⟩⟦_⟧op B
    mk∪ B _ .Alg.⟦_⟧eqn (inl e) = Alg.⟦_⟧eqn B e
    mk∪ _ s .Alg.⟦_⟧eqn (inr e) = s e

    AlgIso∪ : isSet X
      → Iso (Alg (σeq ∪Eqns E) X)
            (Σ[ B ∈ Alg σeq X ] Sat E (Alg.⟨_⟩⟦_⟧op B))
    AlgIso∪ isSetX .Iso.fun B = Alg∪ B , sat∪ B
    AlgIso∪ isSetX .Iso.inv (B , s) = mk∪ B s
    AlgIso∪ isSetX .Iso.sec (B , s) =
      Σ≡Prop (λ B' → isPropSat {E = E} {α = Alg.⟨_⟩⟦_⟧op B'} isSetX)
        (AlgExt isSetX refl)
    AlgIso∪ isSetX .Iso.ret B =
      AlgExt isSetX refl

-- A term over V becomes a *closed* term of σ[V], where each generator is
-- its own constant.  `TmRec-closeTm` says the interpretation of the
-- closed term in a model of `σeq [ V ]adjoin` is the interpretation of the original
-- at the model's points.
module _ {σ : AlgTheorySig ℓ ℓv} {V : Type ℓv} where

  closeTm : {W : Type ℓv} → Tm σ V → Tm (σ ⊕Sig PointedSig V) W
  closeTm (var v) = node (inr v) (λ ())
  closeTm (node op ts) = node (inl op) (λ a → closeTm (ts a))

  module _ {X : Type ℓX}
    (α : ∀ (op : (σ ⊕Sig PointedSig V) .ops)
       → ((σ ⊕Sig PointedSig V) .arities op → X) → X) where

    private
      base : ∀ (op : σ .ops) → (σ .arities op → X) → X
      base op = α (inl op)

      pts : V → X
      pts v = α (inr v) (λ ())

    TmRec-closeTm : {W : Type ℓv} (k : W → X) (M : Tm σ V)
      → TmRec α k (closeTm M) ≡ TmRec base pts M
    TmRec-closeTm k (var v) = cong (α (inr v)) (funExt (λ ()))
    TmRec-closeTm k (node op ts) =
      cong (α (inl op)) (funExt (λ a → TmRec-closeTm k (ts a)))

-- A presentation over a theory: generators V and relations between
-- terms in those generators.
record Presentation (σ : AlgTheorySig ℓ ℓv) (V : Type ℓv) (ℓR : Level)
  : Type (ℓ-max (ℓ-max ℓ ℓv) (ℓ-suc ℓR)) where
  field
    rels : Type ℓR
    rl rr : rels → Tm σ V

open Presentation

module _ {σ : AlgTheorySig ℓ ℓv} {V : Type ℓv} (P : Presentation σ V ℓR)
  where

  -- the relations as equations of `σeq [ V ]adjoin` with no variables
  RelEqns : AlgTheoryEqns (σ ⊕Sig PointedSig V) ℓR ℓv
  RelEqns .eqns = P .rels
  RelEqns .vars _ = ⊥* {ℓv}
  RelEqns .lhs e = closeTm (P .rl e)
  RelEqns .rhs e = closeTm (P .rr e)

  module _ (σeq : AlgTheoryEqns σ ℓ'' ℓv) where

    -- the presented theory: σ, a constant for each generator, and the
    -- relations
    PresEqns' : AlgTheoryEqns (σ ⊕Sig PointedSig V) (ℓ-max ℓ'' ℓR) ℓv
    PresEqns' = σeq [ V ]adjoin ∪Eqns RelEqns

    -- the level the presented model lives at.  Models at this level are
    -- the stages of the Yoneda argument, so it is named rather than
    -- inlined.
    ℓPres : Level
    ℓPres = ℓFree (ℓ-max ℓ ℓv) (ℓ-max ℓ'' ℓR) ℓv

    -- the presented model
    Presented : Type ℓPres
    Presented = FreeModel PresEqns' (⊥* {ℓv})

    PresentedOb : Category.ob (MOD PresEqns' ℓPres)
    PresentedOb = FreeOb PresEqns' (⊥* {ℓv})

    PresentedAlg : Alg PresEqns' Presented
    PresentedAlg = FreeAlg PresEqns' (⊥* {ℓv})

    -- the generators, as elements
    gen : V → Presented
    gen v = Alg.⟨_⟩⟦_⟧op PresentedAlg (inr v) (λ ())

    -- the underlying σ-model, forgetting both the constants and the
    -- relations
    PresentedσAlg : Alg σeq Presented
    PresentedσAlg = forgetPoints σeq V
      (Presented , trunc) (Alg∪ (σeq [ V ]adjoin) RelEqns PresentedAlg)

    -- The relations hold between the generators.  This is the only
    -- place the added equations are used, and it is where "equation
    -- with no variables" pays off: there is nothing to instantiate, so
    -- the relation lands on `gen` and nowhere else.
    relGen : (e : P .rels)
      → TmRec (Alg.⟨_⟩⟦_⟧op PresentedσAlg) gen (P .rl e)
        ≡ TmRec (Alg.⟨_⟩⟦_⟧op PresentedσAlg) gen (P .rr e)
    relGen e =
      sym (TmRec-closeTm α (λ ()) (P .rl e))
      ∙ Alg.⟦_⟧eqn PresentedAlg (inr e) (λ ())
      ∙ TmRec-closeTm α (λ ()) (P .rr e)
      where α = Alg.⟨_⟩⟦_⟧op PresentedAlg

    -- A point of a model `A` is an interpretation of the generators at
    -- which the relations hold: for the theory of commutative
    -- k-algebras this is exactly a point of the affine variety.
    module _ {X : Type ℓX} (isSetX : isSet X) (A : Alg σeq X) where
      private
        module A = Alg A

      Points : Type (ℓ-max (ℓ-max ℓv ℓR) ℓX)
      Points = Σ[ ρ ∈ (V → X) ]
        ((e : P .rels) → TmRec A.⟨_⟩⟦_⟧op ρ (P .rl e)
                       ≡ TmRec A.⟨_⟩⟦_⟧op ρ (P .rr e))

      isSetPoints : isSet Points
      isSetPoints = isSetΣSndProp (isSet→ isSetX)
        (λ _ → isPropΠ λ _ → isSetX _ _)

      σHom : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓv) (ℓ-max ℓ'' ℓR))
                         (ℓ-max (ℓ-suc ℓv) ℓX))
      σHom = Σ[ f ∈ (Presented → X) ] Homo σeq f PresentedσAlg A

      private
        module _ ((ρ , sat) : Points) where
          N[V] : Alg (σeq [ V ]adjoin) X
          N[V] = withPoints σeq V (X , isSetX) A ρ

          satRel : Sat RelEqns (Alg.⟨_⟩⟦_⟧op N[V])
          satRel e k =
            TmRec-closeTm (Alg.⟨_⟩⟦_⟧op N[V]) k (P .rl e)
            ∙ sat e
            ∙ sym (TmRec-closeTm (Alg.⟨_⟩⟦_⟧op N[V]) k (P .rr e))

          N : Alg PresEqns' X
          N = mk∪ (σeq [ V ]adjoin) RelEqns N[V] satRel

          mor : Presented → X
          mor = rec PresEqns' isSetX N (λ ())

          morHomo : Homo PresEqns' mor PresentedAlg N
          morHomo = recHomo PresEqns' isSetX N (λ ())

        -- a σ-homomorphism sending the generators to `ρ` is a
        -- homomorphism for the constants too: their arity is empty, so
        -- the two arguments agree
        constHomo : ((ρ , sat) : Points) (f : Presented → X)
          → Homo σeq f PresentedσAlg A → (∀ v → f (gen v) ≡ ρ v)
          → Homo PresEqns' f PresentedAlg (N (ρ , sat))
        constHomo (ρ , sat) f ϕ fβ .Homo.op-hom (inl op) x y eq =
          Homo.op-hom ϕ op x y eq
        constHomo (ρ , sat) f ϕ fβ .Homo.op-hom (inr v) x y eq =
          cong f (eq ∙ cong (Alg.⟨_⟩⟦_⟧op PresentedAlg (inr v))
                       (funExt (λ ())))
          ∙ fβ v

      toPoints : σHom → Points
      toPoints (f , ϕ) .fst v = f (gen v)
      toPoints (f , ϕ) .snd e =
        sym (Homo-Tm σeq ϕ gen (P .rl e))
        ∙ cong f (relGen e)
        ∙ Homo-Tm σeq ϕ gen (P .rr e)

      UPPresented : Iso σHom Points
      UPPresented .Iso.fun = toPoints
      UPPresented .Iso.inv pt .fst = mor pt
      UPPresented .Iso.inv pt .snd .Homo.op-hom op x y eq =
        Homo.op-hom (morHomo pt) (inl op) x y eq
      UPPresented .Iso.sec pt =
        Σ≡Prop (λ _ → isPropΠ λ _ → isSetX _ _) refl
      UPPresented .Iso.ret (f , ϕ) =
        Σ≡Prop (λ _ → isPropHomo σeq isSetX)
          (funExt λ x → sym
            (recUniq PresEqns' isSetX (N (toPoints (f , ϕ))) (λ ()) f
              (constHomo (toPoints (f , ϕ)) f ϕ (λ _ → refl)) (λ ()) x))
