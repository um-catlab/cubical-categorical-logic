{-# OPTIONS --safe #-}

-- defines adjoint for monotone functions and morphisms in the Poset Category
-- where each morphism has left and right adjoints

module Cubical.Categories.Instances.Preorders.Monotone.Adjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Binary.Preorder
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties

open import Cubical.Categories.Instances.Preorders.Monotone


private
  variable
    ℓ ℓ' : Level


module _ {ℓ ℓ' : Level} where

  -- the Galois Connection between Posets
  -- adjoints for monotone functions
  record _⊣_ {X Y : Preorder ℓ ℓ'}
             (L : MonFun X Y) (R : MonFun Y X) : Type (ℓ-max ℓ ℓ') where
    private
      module 𝕏 = PreorderStr (X .snd)
      module 𝕐 = PreorderStr (Y .snd)
    field
      adjIff : ∀ {x y} → Iso
        ((L $ x) 𝕐.≤ y)
        (x 𝕏.≤ (R $ y))

  -- monotone functions that have left and right adjoint
  HasLeftAdj : {X Y : Preorder ℓ ℓ'} → (f : MonFun X Y) → Type ((ℓ-max ℓ ℓ'))
  HasLeftAdj {X} {Y} f = Σ[ L ∈ MonFun Y X ] (L ⊣ f)

  open isUnivalent
  open IsPreorder
  open _⊣_
  open Iso

  -- when assuming that the relation on X is antisymmetric,
  -- we get that adjoints are unique
  isPropHasLeftAdj : {X Y : Preorder ℓ ℓ'}
    → (isUnivalent X)
    → (f : MonFun X Y)
    → isProp (HasLeftAdj f)
  isPropHasLeftAdj {X} {Y} po f = λ (l1 , l1⊣f) (l2 , l2⊣f ) →
    let Xpo = PreorderStr.isPreorder (X .snd)
        l1≡l2 = eqMon l1 l2 (funExt (λ y →
                  (posetAntisym po) (l1 $ y) (l2 $ y)
                  -- l1(y) ≤ l2(y)
                  ( l1⊣f .adjIff .inv
                    (l2⊣f .adjIff .fun (Xpo .is-refl (l2 $ y))))
                  -- l2(y) ≤ l1(y)
                  (l2⊣f .adjIff .inv
                    (l1⊣f .adjIff .fun (Xpo .is-refl (l1 $ y))))
                ))
        ≤YProp = is-prop-valued (PreorderStr.isPreorder (Y .snd))
    in
    ΣPathP ( l1≡l2  ,
      isProp→PathP (λ i →
        λ l1⊣f l2⊣f →
          λ j →
            record {
              adjIff = λ {y} {x} →
              (Iso≡Set
                (isProp→isSet (Xpo .is-prop-valued _ _))
                (isProp→isSet (≤YProp _ _))
                (l1⊣f .adjIff) (l2⊣f .adjIff)
                (λ ly≤x → (≤YProp y (f $ x)) _ _)
                (λ y≤fx → (Xpo .is-prop-valued ((l1≡l2 i) $ y) x) _ _)
              j)
            }
      ) _ _
    )
  HasRightAdj : {X Y : Preorder ℓ ℓ'} → (f : MonFun X Y) → Type ((ℓ-max ℓ ℓ'))
  HasRightAdj {X} {Y} f = Σ[ R ∈ MonFun Y X ] (f ⊣ R)


  isPropHasRightAdj : {X Y : Preorder ℓ ℓ'}
    → (isUnivalent X)
    → (f : MonFun X Y)
    → isProp (HasRightAdj f)
  isPropHasRightAdj {X} {Y} po f = λ (r1 , f⊣r1) (r2 , f⊣r2) →
    let Xpo = PreorderStr.isPreorder (X .snd)
        r1≡r2 = eqMon r1 r2 (funExt (λ y →
                  (posetAntisym po) (r1 $ y) (r2 $ y)
                  -- r1(y) ≤ r2(y)
                  (f⊣r2 .adjIff .fun
                    (f⊣r1 .adjIff .inv (Xpo .is-refl (r1 $ y))))
                  -- r2(y) ≤ r1(y)
                  (f⊣r1 .adjIff .fun
                    (f⊣r2 .adjIff .inv (Xpo .is-refl (r2 $ y))))
                ))
        ≤YProp = is-prop-valued (PreorderStr.isPreorder (Y .snd))
    in
    ΣPathP ( r1≡r2 ,
      isProp→PathP (λ i →
        λ f⊣r1 f⊣r2 →
          λ j →
            record {
              adjIff = λ {x} {y} →
              (Iso≡Set
                (isProp→isSet (≤YProp _ _))
                (isProp→isSet (Xpo .is-prop-valued _ _))
                (f⊣r1 .adjIff)
                (f⊣r2 .adjIff)
                (λ fx≤y → (Xpo .is-prop-valued x ((r1≡r2 i) $ y)) _ _)
                (λ x≤ry → (≤YProp (f $ x) y) _ _)
              j)
            }
      ) _ _
    )

  record HasBothAdj {X Y : Preorder ℓ ℓ'}
    (f : MonFun X Y) : Type ((ℓ-max ℓ ℓ')) where
    field
      left-adj : HasLeftAdj f
      right-adj : HasRightAdj f

  open HasBothAdj

  isPropHasBothAdj : {X Y : Preorder ℓ ℓ'}
    → (isUnivalent X)
    → (f : MonFun X Y)
    → isProp (HasBothAdj f)
  isPropHasBothAdj pox f = λ adj1 adj2 →
    λ i → record {
      left-adj = isPropHasLeftAdj pox f (adj1 .left-adj) (adj2 .left-adj) i ;
      right-adj = isPropHasRightAdj pox f (adj1 .right-adj) (adj2 .right-adj) i
    }

  MonId⊣MonId : {X : Preorder ℓ ℓ'} → MonId {X = X} ⊣ MonId {X = X}
  MonId⊣MonId {X} =
    record { adjIff = iso (λ h → h) (λ h → h) ( λ _ → refl)  (λ _ → refl) }

  IdHasLeftAdj : {X : Preorder ℓ ℓ'} → HasLeftAdj {X} {X} MonId
  IdHasLeftAdj {X} = MonId , MonId⊣MonId

  IdHasRightAdj : {X : Preorder ℓ ℓ'} → HasRightAdj {X} {X} MonId
  IdHasRightAdj {X} = MonId , MonId⊣MonId

  IdHasBothAdj : {X : Preorder ℓ ℓ'} → HasBothAdj {X} {X} MonId
  IdHasBothAdj {X} = record {
    left-adj = IdHasLeftAdj ;
    right-adj = IdHasRightAdj }

  CompHasLeftAdj : {X Y Z : Preorder ℓ ℓ'} →
    {f : MonFun X Y} → {g : MonFun Y Z } →
    HasLeftAdj f → HasLeftAdj g → HasLeftAdj (MonComp f g)
  CompHasLeftAdj (l1 , l1⊣f) (l2 , l2⊣g) = MonComp l2 l1 ,
      record { adjIff = compIso (l1⊣f .adjIff) (l2⊣g .adjIff) }

  CompHasRightAdj : {X Y Z : Preorder ℓ ℓ'} →
    {f : MonFun X Y} → {g : MonFun Y Z } →
    HasRightAdj f → HasRightAdj g → HasRightAdj (MonComp f g)
  CompHasRightAdj (r1 , f⊣r1) (r2 , g⊣r2) = MonComp r2 r1 ,
      record { adjIff = compIso (g⊣r2 .adjIff) (f⊣r1 .adjIff) }

  CompHasBothAdj : {X Y Z : Preorder ℓ ℓ'} →
    {f : MonFun X Y} → {g : MonFun Y Z } →
    HasBothAdj f → HasBothAdj g → HasBothAdj (MonComp f g)
  CompHasBothAdj f-adj g-adj = record {
    left-adj = CompHasLeftAdj (f-adj .left-adj) (g-adj .left-adj) ;
    right-adj = CompHasRightAdj (f-adj .right-adj) (g-adj .right-adj) }
