-- Coproducts of presented models.
--
-- The disjoint union of the generators and of the relations presents
-- the coproduct: for commutative k-algebras this is
--
--   k[V]/I ⊗ k[W]/J  =  k[V ⊎ W]/(I ⊎ J),
--
-- so the tensor product of presented models needs no tensor product
-- construction.  A point of `P ⊎Pres Q` in a model is a pair of a point
-- of `P` and a point of `Q`, and composing with the universal property
-- of the presented model turns that into the hom-set isomorphism
-- `Hom(A ⊗ B , -) ≅ Hom(A , -) × Hom(B , -)`.
module Cubical.Algebra.Theory.Presentation.Coproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Constructions
open import Cubical.Algebra.Theory.Presentation
open import Cubical.Algebra.Theory.Free.Explicit using (trunc)

private
  variable
    ℓ ℓ' ℓ'' ℓR ℓv ℓX : Level

open Presentation

module _ {σ : AlgTheorySig ℓ ℓv} where

  -- generators and relations both added disjointly
  _⊎Pres_ : {V W : Type ℓv}
    → Presentation σ V ℓR → Presentation σ W ℓR
    → Presentation σ (V ⊎ W) ℓR
  (P ⊎Pres Q) .rels = P .rels ⊎ Q .rels
  (P ⊎Pres Q) .rl (inl e) = renTm inl (P .rl e)
  (P ⊎Pres Q) .rl (inr e) = renTm inr (Q .rl e)
  (P ⊎Pres Q) .rr (inl e) = renTm inl (P .rr e)
  (P ⊎Pres Q) .rr (inr e) = renTm inr (Q .rr e)

  module _ {V W : Type ℓv}
    (P : Presentation σ V ℓR) (Q : Presentation σ W ℓR)
    (σeq : AlgTheoryEqns σ ℓ'' ℓv)
    {X : Type ℓX} (isSetX : isSet X) (A : Alg σeq X)
    where
    private
      module A = Alg A
      α = A.⟨_⟩⟦_⟧op

      isPropSatP : (ρ : V → X)
        → isProp ((e : P .rels) → TmRec α ρ (P .rl e) ≡ TmRec α ρ (P .rr e))
      isPropSatP ρ = isPropΠ λ _ → isSetX _ _

      isPropSatQ : (ρ : W → X)
        → isProp ((e : Q .rels) → TmRec α ρ (Q .rl e) ≡ TmRec α ρ (Q .rr e))
      isPropSatQ ρ = isPropΠ λ _ → isSetX _ _

    -- a point of the disjoint union is a pair of points: the relations
    -- of `P` only constrain the `inl` half of the assignment, those of
    -- `Q` only the `inr` half
    PointsIso⊎ : Iso (Points (P ⊎Pres Q) σeq isSetX A)
                     (Points P σeq isSetX A × Points Q σeq isSetX A)
    PointsIso⊎ .Iso.fun (ρ , sat) =
      ( ( ρ ∘ inl
        , (λ e → TmRec-renTm α ρ inl (P .rl e)
               ∙ sat (inl e)
               ∙ sym (TmRec-renTm α ρ inl (P .rr e))) )
      , ( ρ ∘ inr
        , (λ e → TmRec-renTm α ρ inr (Q .rl e)
               ∙ sat (inr e)
               ∙ sym (TmRec-renTm α ρ inr (Q .rr e))) ) )
    PointsIso⊎ .Iso.inv ((ρ₁ , s₁) , (ρ₂ , s₂)) =
      ( ρ
      , λ { (inl e) → sym (TmRec-renTm α ρ inl (P .rl e))
                    ∙ s₁ e
                    ∙ TmRec-renTm α ρ inl (P .rr e)
          ; (inr e) → sym (TmRec-renTm α ρ inr (Q .rl e))
                    ∙ s₂ e
                    ∙ TmRec-renTm α ρ inr (Q .rr e) } )
      where
        ρ : V ⊎ W → X
        ρ (inl v) = ρ₁ v
        ρ (inr w) = ρ₂ w
    PointsIso⊎ .Iso.sec ((ρ₁ , s₁) , (ρ₂ , s₂)) =
      ΣPathP ( Σ≡Prop isPropSatP refl , Σ≡Prop isPropSatQ refl )
    PointsIso⊎ .Iso.ret (ρ , sat) =
      Σ≡Prop (λ _ → isPropΠ λ _ → isSetX _ _)
        (funExt λ { (inl v) → refl ; (inr w) → refl })

    -- the presented model of `P ⊎Pres Q` is the coproduct of the
    -- presented models of `P` and of `Q`
    σHomIso⊎ : Iso (σHom (P ⊎Pres Q) σeq isSetX A)
                   (σHom P σeq isSetX A × σHom Q σeq isSetX A)
    σHomIso⊎ = compIso (UPPresented (P ⊎Pres Q) σeq isSetX A)
      (compIso PointsIso⊎
        (invIso (prodIso (UPPresented P σeq isSetX A)
                         (UPPresented Q σeq isSetX A))))

  -- the two coprojections, as the halves of the identity homomorphism
  module _ {V W : Type ℓv}
    (P : Presentation σ V ℓR) (Q : Presentation σ W ℓR)
    (σeq : AlgTheoryEqns σ ℓ'' ℓv)
    where
    private
      A : Alg σeq (Presented (P ⊎Pres Q) σeq)
      A = PresentedσAlg (P ⊎Pres Q) σeq

      idσHom : σHom (P ⊎Pres Q) σeq trunc A
      idσHom = (λ x → x) , idHomo σeq

    ι₁ : σHom P σeq trunc A
    ι₁ = σHomIso⊎ P Q σeq trunc A .Iso.fun idσHom .fst

    ι₂ : σHom Q σeq trunc A
    ι₂ = σHomIso⊎ P Q σeq trunc A .Iso.fun idσHom .snd
