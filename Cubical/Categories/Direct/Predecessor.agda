{-# OPTIONS --lossy-unification #-}
-- Predecessor presentation of ▷: when the strict downset ↡x is
-- represented by a predecessor p, ▷Psh P at x is P at p; at a minimal
-- object ▷Psh P is trivial.
module Cubical.Categories.Direct.Predecessor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit* ; tt*)
open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.StrictDownset
  using ( ↡Psh ; ▷Psh ; next
        ; ▷Fam ; nextFam ; löbFam ; löbFam-unfold ; löbFam-uniq-unfold )
import Cubical.Categories.Presheaf.Family.Base as FamBase

private
  variable
    ℓ ℓ' ℓD ℓP : Level

module _ {C : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'}
         (dir : DirectStr {C = C} Wo) where
  open Category C
  open Functor
  open PshHomStrict
  open DirectNotation dir

  -- p is a predecessor of x when it represents the strict downset ↡x
  record isPredOf (x p : ob) : Type (ℓ-max ℓ ℓ') where
    field
      ρ   : C [ p , x ]
      p≺x : p ≺ x

    ↡fun : ∀ y → C [ y , p ] → ⟨ ↡Psh dir x .F-ob y ⟩
    ↡fun y f = (f ⋆ ρ) , ≺-precomp f p≺x

    field
      univ : ∀ y → isEquiv (↡fun y)

    ↡eq : ∀ y → C [ y , p ] ≃ ⟨ ↡Psh dir x .F-ob y ⟩
    ↡eq y = ↡fun y , univ y

  module _ {ℓP} (P : Presheaf C ℓP) where
    private
      module P = PresheafNotation P

    -- ▷ at a minimal object is trivial
    module _ {x : ob} (min : ∀ y → ¬ (y ≺ x)) where
      ▷min : isContr ⟨ ▷Psh dir P .F-ob x ⟩
      ▷min .fst = pshhom
        (λ y (g , q) → ⊥.rec (min y q))
        (λ y' y h (g , q) w hyp → ⊥.rec (min y q))
      ▷min .snd α = makePshHomStrictPath
        (funExt λ y → funExt λ (g , q) → ⊥.rec (min y q))

    -- ▷ at x computes as P at the predecessor
    module _ {x p : ob} (pred : isPredOf x p) where
      open isPredOf pred

      ▷pred : Iso ⟨ ▷Psh dir P .F-ob x ⟩ ⟨ P .F-ob p ⟩
      ▷pred .Iso.fun α = α .N-ob p (ρ , p≺x)
      ▷pred .Iso.inv v = pshhom
        (λ y w → invEq (↡eq y) w P.⋆ v)
        (λ y' y h w' w hyp →
          sym (P.⋆Assoc h (invEq (↡eq y) w') v)
          ∙ cong (P._⋆ v)
              (sym (retEq (↡eq y') (h ⋆ invEq (↡eq y) w'))
               ∙ cong (invEq (↡eq y'))
                   (Σ≡Prop (λ _ → isProp≺ _ _)
                      (⋆Assoc h (invEq (↡eq y) w') ρ
                       ∙ cong (h ⋆_) (cong fst (secEq (↡eq y) w')))
                    ∙ hyp)))
      ▷pred .Iso.sec v =
        cong (P._⋆ v)
          (cong (invEq (↡eq p)) (Σ≡Prop (λ _ → isProp≺ _ _) (sym (⋆IdL ρ)))
           ∙ retEq (↡eq p) id)
        ∙ P.⋆IdL v
      ▷pred .Iso.ret α = makePshHomStrictPath (funExt λ y → funExt λ w →
        α .N-hom y p (invEq (↡eq y) w) (ρ , p≺x) _ refl
        ∙ cong (α .N-ob y) (secEq (↡eq y) w))

      -- under ▷pred, next is restriction along ρ
      ▷pred-next : (u : ⟨ P .F-ob x ⟩)
        → ▷pred .Iso.fun (next dir P .N-ob x u) ≡ ρ P.⋆ u
      ▷pred-next u = refl

  -- the family ▷ in predecessor form
  module _ {ℓF} (A : ob → hSet (ℓ-max ℓF (ℓ-max ℓ ℓ'))) where
    private
      GA = FamBase.Cofree {ℓ = ℓF} C .F-ob A

    ▷FamPred : {x p : ob} → isPredOf x p
      → Iso ⟨ ▷Fam dir {ℓF = ℓF} A x ⟩ ((z : ob) → C [ z , p ] → ⟨ A z ⟩)
    ▷FamPred = ▷pred GA

    ▷FamMin : {x : ob} → (∀ y → ¬ (y ≺ x))
      → isContr ⟨ ▷Fam dir {ℓF = ℓF} A x ⟩
    ▷FamMin = ▷min GA

    -- under ▷FamPred, nextFam is the constant closure, so
    -- löbFam-unfold computes in predecessor form
    ▷FamPred-next : {x p : ob} (pr : isPredOf x p) (t : ∀ z → ⟨ A z ⟩)
      → ▷FamPred pr .Iso.fun (nextFam dir {ℓF = ℓF} A t x)
        ≡ (λ z _ → t z)
    ▷FamPred-next pr t = refl

  -- every object is minimal or has a predecessor
  data ▷View (x : ob) : Type (ℓ-max ℓ ℓ') where
    minimal : (∀ y → ¬ (y ≺ x)) → ▷View x
    hasPred : (p : ob) → isPredOf x p → ▷View x

  Predecessors : Type (ℓ-max ℓ ℓ')
  Predecessors = ∀ x → ▷View x

  -- Löb induction through the predecessor presentation of ▷Fam
  module _ (pv : Predecessors) {ℓF}
           (A : ob → hSet (ℓ-max ℓF (ℓ-max ℓ ℓ'))) where

    LaterPredAt : {x : ob} → ▷View x → Type (ℓ-max ℓF (ℓ-max ℓ ℓ'))
    LaterPredAt (minimal _)   = Unit*
    LaterPredAt (hasPred p _) = (z : ob) → C [ z , p ] → ⟨ A z ⟩

    LaterPred : ob → Type (ℓ-max ℓF (ℓ-max ℓ ℓ'))
    LaterPred x = LaterPredAt (pv x)

    LaterPredIsoAt : {x : ob} (v : ▷View x)
      → Iso ⟨ ▷Fam dir {ℓF = ℓF} A x ⟩ (LaterPredAt v)
    LaterPredIsoAt (minimal m) .Iso.fun _ = tt*
    LaterPredIsoAt (minimal m) .Iso.inv _ = ▷FamMin A m .fst
    LaterPredIsoAt (minimal m) .Iso.sec _ = refl
    LaterPredIsoAt (minimal m) .Iso.ret β = ▷FamMin A m .snd β
    LaterPredIsoAt (hasPred p pr) = ▷FamPred A pr

    LaterPredIso : ∀ x → Iso ⟨ ▷Fam dir {ℓF = ℓF} A x ⟩ (LaterPred x)
    LaterPredIso x = LaterPredIsoAt (pv x)

    module LöbPred (φ : ∀ x → LaterPred x → ⟨ A x ⟩) where
      private
        φ▷ : ∀ x → ⟨ ▷Fam dir {ℓF = ℓF} A x ⟩ → ⟨ A x ⟩
        φ▷ x β = φ x (LaterPredIso x .Iso.fun β)

      nextPred : (∀ z → ⟨ A z ⟩) → ∀ x → LaterPred x
      nextPred t x = LaterPredIso x .Iso.fun (nextFam dir {ℓF = ℓF} A t x)

      fix : ∀ x → ⟨ A x ⟩
      fix = löbFam dir {ℓF = ℓF} A φ▷

      unfold : ∀ x → fix x ≡ φ x (nextPred fix x)
      unfold = löbFam-unfold dir {ℓF = ℓF} A φ▷

      uniq : (t : ∀ x → ⟨ A x ⟩)
        → (∀ x → t x ≡ φ x (nextPred t x))
        → t ≡ fix
      uniq = löbFam-uniq-unfold dir {ℓF = ℓF} A φ▷
