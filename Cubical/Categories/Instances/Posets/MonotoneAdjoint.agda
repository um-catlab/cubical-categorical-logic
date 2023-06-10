{-# OPTIONS --safe #-}

-- defines adjoint for monotone functions and morphisms in the Poset Category
-- where each morphism has left and right adjoints

module Cubical.Categories.Instances.Posets.MonotoneAdjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Binary.Poset
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties

open import Cubical.Categories.Instances.Posets.Monotone


private
  variable
    ℓ ℓ' : Level


module _ {ℓ ℓ' : Level} where

  -- the Galois Connection between Posets
  -- adjoints for monotone functions
  record _⊣_ {X Y : Poset ℓ ℓ'}
             (L : MonFun X Y) (R : MonFun Y X) : Type (ℓ-max ℓ ℓ') where
    field
      adjIff : ∀ {x y} → Iso
        ((PosetStr._≤_ (Y .snd)) (MonFun.f L x) y)
        ((PosetStr._≤_ (X .snd)) x (MonFun.f R y))

  -- monotone functions that have left and right adjoint
  record MonFunAdj (X Y : Poset ℓ ℓ') : Type ((ℓ-max ℓ ℓ')) where
    field
      morphism : MonFun X Y
      left-adj : Σ[ L ∈ MonFun Y X ] ∥ (L ⊣ morphism) ∥₁
      right-adj : Σ[ R ∈ MonFun Y X ] ∥ (morphism ⊣ R) ∥₁

  MonId⊣MonId : {X : Poset ℓ ℓ'} → MonId {X = X} ⊣ MonId {X = X}
  MonId⊣MonId {X} =
    record { adjIff = iso (λ h → h) (λ h → h) ( λ _ → refl)  (λ _ → refl) }

  open MonFunAdj
  open _⊣_

  MonIdAdj : {X : Poset ℓ ℓ'} → MonFunAdj X X
  MonIdAdj {X} = record {
    morphism = MonId ;
    left-adj = MonId , ∣ MonId⊣MonId ∣₁ ;
    right-adj =  MonId , ∣ MonId⊣MonId ∣₁ }

  MonCompAdj : {X Y Z : Poset ℓ ℓ'} ->
    MonFunAdj X Y -> MonFunAdj Y Z -> MonFunAdj X Z
  MonCompAdj f g = record {
    morphism = MonComp (f .morphism) (g .morphism) ;
    left-adj = MonComp (fst (g .left-adj)) (fst (f .left-adj)) ,
      rec2  isPropPropTrunc
        (λ l1 l2 → ∣ record { adjIff = compIso (l1 .adjIff) (l2 .adjIff) } ∣₁)
        (snd (f .left-adj)) (snd (g .left-adj))  ;
    right-adj = MonComp (fst (g .right-adj)) (fst (f .right-adj)) ,
      rec2  isPropPropTrunc
        (λ r1 r2 → ∣ record { adjIff = compIso (r1 .adjIff) (r2 .adjIff) } ∣₁)
        (snd (g .right-adj)) (snd (f .right-adj))  }


  -- equality of underlying monotone functions
  -- gives us equality of records
  eqMonAdj : {X Y : Poset ℓ ℓ'} → (f g : MonFunAdj X Y) →
    f .morphism ≡ g .morphism →
    fst (f .left-adj) ≡ fst (g .left-adj) →
    fst (f .right-adj) ≡ fst (g . right-adj) →
    f ≡ g
  morphism (eqMonAdj f g fm≡gm fl≡gl fr≡gr i) = fm≡gm i
  left-adj (eqMonAdj {X} {Y} f g fm≡gm fl≡gl fr≡gr i) =
    (ΣPathPProp
      {A = λ _ → MonFun Y X}
      {B = λ i l → ∥ l ⊣ (fm≡gm i) ∥₁ }
      {u = (f .left-adj)}
      {v = (g .left-adj)}
      (λ l → isPropPropTrunc )
      fl≡gl
    ) i
  right-adj (eqMonAdj {X} {Y} f g fm≡gm fl≡gl fr≡gr i) =
    (ΣPathPProp
      {A = λ _ → MonFun Y X}
      {B = λ i r → ∥ (fm≡gm i) ⊣ r ∥₁ }
      {u = (f .right-adj)}
      {v = (g .right-adj)}
      (λ r → isPropPropTrunc )
      fr≡gr
    ) i

  MonFunAdjIsSet : {X Y : Poset ℓ ℓ'} → isSet (MonFunAdj X Y)
  MonFunAdjIsSet {X} {Y}  x y p q = w
    where
      w : _
      morphism (w i j) = MonFunIsSet (x .morphism) (y .morphism)
        ( cong morphism p) (cong morphism q) i j
      left-adj (w i j) = isSet→SquareP
        (λ i j → (isSetΣSndProp
          (MonFunIsSet {X = Y} {Y = X})
          (λ L → isPropPropTrunc {A = L ⊣ morphism (w i j)})))
        (cong left-adj p) (cong left-adj q)
        refl refl i j
      right-adj (w i j) = isSet→SquareP
        (λ i j → (isSetΣSndProp (MonFunIsSet {X = Y} {Y = X})
          (λ R → isPropPropTrunc {A = morphism (w i j) ⊣ R})))
        (cong right-adj p) (cong right-adj q)
        refl refl i j
