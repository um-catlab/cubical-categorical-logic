module Gluing.BiCartesianClosedCategory.StackParametricity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.List.Properties
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Instances.Sets.Cartesian
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Forded
  as FreeBiCCC
open import Gluing.BiCartesianClosedCategory.BinaryLogicalRelation

data OB : Type where
  elem : OB
  stack : OB

data MOR : Type where
  emptyStack : MOR
  push : MOR

open QuiverOver

STACK-Q : +×⇒Quiver ℓ-zero ℓ-zero
STACK-Q .+×⇒Quiver.ob = OB
STACK-Q .+×⇒Quiver.Q .mor = MOR
STACK-Q .+×⇒Quiver.Q .dom emptyStack = ⊤
STACK-Q .+×⇒Quiver.Q .dom push = (↑ elem) × (↑ stack)
STACK-Q .+×⇒Quiver.Q .cod emptyStack = ↑ stack
STACK-Q .+×⇒Quiver.Q .cod push = ↑ stack

private
  module FREE =
    BiCartesianClosedCategory (FreeBiCartesianClosedCategory STACK-Q)

HeadFirst : CartesianFunctor FREE.CC (SET ℓ-zero)
HeadFirst = FreeBiCCC.recCF STACK-Q SETBiCCC
  (FreeBiCCC.mkElimInterpᴰ
    (λ { elem → Bool , isSetBool
       ; stack → List Bool , isOfHLevelList 0 isSetBool })
    λ { emptyStack → λ _ → []
      ; push → λ (b , xs) → b ∷ xs })

ReverseStored : CartesianFunctor FREE.CC (SET ℓ-zero)
ReverseStored = FreeBiCCC.recCF STACK-Q SETBiCCC
  (FreeBiCCC.mkElimInterpᴰ
    (λ { elem → Bool , isSetBool
       ; stack → List Bool , isOfHLevelList 0 isSetBool })
    λ { emptyStack → λ _ → []
      ; push → λ (b , xs) → xs ++ (b ∷ []) })

StackRelationGenerators :
  LogicalRelationGenerators STACK-Q SETBiCCC EqSETᴰBCCCⱽ
    ×SetsCF HeadFirst ReverseStored
StackRelationGenerators =
  FreeBiCCC.mkElimInterpᴰ
    (λ { elem (b , c) →
           (b ≡ c) , isProp→isSet (isSetBool _ _)
       ; stack (xs , ys) →
           (xs ≡ rev ys) ,
           isProp→isSet
             (isOfHLevelList 0 isSetBool _ _) })
    λ
      { emptyStack → λ _ _ → refl
      ; push → λ ((b , xs) , (c , ys)) (p , q) →
          cong₂ _∷_ p q ∙ sym (rev-snoc ys c)
      }

StackLogicalRelation =
  logicalRelation STACK-Q SETBiCCC EqSETᴰBCCCⱽ
    ×SetsCF HeadFirst ReverseStored StackRelationGenerators
