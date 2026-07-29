module Gluing.BiCartesianClosedCategory.StackParametricity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.List.Properties
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma as Sigma hiding (_×_)
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Instances.Sets.Cartesian
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Forded
  as FreeBiCCC renaming ([_,_] to [_,+_])
open import Gluing.BiCartesianClosedCategory.BinaryLogicalRelation

open Functor
open Section

data OB : Type where
  elem : OB
  stack : OB

data MOR : Type where
  emptyStack : MOR
  push : MOR
  pop : MOR

open QuiverOver

StackQuiver : +×⇒Quiver ℓ-zero ℓ-zero
StackQuiver .+×⇒Quiver.ob = OB
StackQuiver .+×⇒Quiver.Q .mor = MOR
StackQuiver .+×⇒Quiver.Q .dom emptyStack = ⊤
StackQuiver .+×⇒Quiver.Q .dom push = (↑ elem) × (↑ stack)
StackQuiver .+×⇒Quiver.Q .dom pop = ↑ stack
StackQuiver .+×⇒Quiver.Q .cod emptyStack = ↑ stack
StackQuiver .+×⇒Quiver.Q .cod push = ↑ stack
StackQuiver .+×⇒Quiver.Q .cod pop = ⊤ + ((↑ elem) × (↑ stack))

private
  module FREE =
    BiCartesianClosedCategory
      (FreeBiCartesianClosedCategory StackQuiver)

headPop : List Bool →
  Lift ℓ-zero Unit ⊎ Σ Bool (λ _ → List Bool)
headPop [] = inl tt*
headPop (b ∷ xs) = inr (b , xs)

reversePoppedStack :
  Lift ℓ-zero Unit ⊎ Σ Bool (λ _ → List Bool) →
  Lift ℓ-zero Unit ⊎ Σ Bool (λ _ → List Bool)
reversePoppedStack (inl u) = inl u
reversePoppedStack (inr (b , xs)) = inr (b , rev xs)

reversePop : List Bool →
  Lift ℓ-zero Unit ⊎ Σ Bool (λ _ → List Bool)
reversePop ys = reversePoppedStack (headPop (rev ys))

HeadFirst : CartesianFunctor FREE.CC (SET ℓ-zero)
HeadFirst = FreeBiCCC.recCF StackQuiver SETBiCCC
  (FreeBiCCC.mkElimInterpᴰ
    (λ { elem → Bool , isSetBool
       ; stack → List Bool , isOfHLevelList 0 isSetBool })
    λ { emptyStack → λ _ → []
      ; push → λ (b , xs) → b ∷ xs
      ; pop → headPop })

ReverseStored : CartesianFunctor FREE.CC (SET ℓ-zero)
ReverseStored = FreeBiCCC.recCF StackQuiver SETBiCCC
  (FreeBiCCC.mkElimInterpᴰ
    (λ { elem → Bool , isSetBool
       ; stack → List Bool , isOfHLevelList 0 isSetBool })
    λ { emptyStack → λ _ → []
      ; push → λ (b , xs) → xs ++ (b ∷ [])
      ; pop → reversePop })

StackRelationGenerators :
  LogicalRelationGenerators StackQuiver SETBiCCC EqSETᴰBCCCⱽ
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
      ; pop → λ
        { ([] , ys) q →
            inl ((tt* , tt*) ,
              ΣPathP (refl ,
                cong (λ zs → reversePoppedStack (headPop zs)) q) ,
              tt*)
        ; ((b ∷ xs) , ys) q →
            inr (((b , xs) , (b , rev xs)) ,
              ΣPathP (refl ,
                cong (λ zs → reversePoppedStack (headPop zs)) q) ,
              refl , sym (rev-rev xs))
        }
      }

StackLogicalRelation =
  logicalRelation StackQuiver SETBiCCC EqSETᴰBCCCⱽ
    ×SetsCF HeadFirst ReverseStored StackRelationGenerators

stack-representation-independence :
  (client : FREE.C [ ⊤ , (↑ stack) ]) →
  HeadFirst .fst .F-hom client tt* ≡
    rev (ReverseStored .fst .F-hom client tt*)
stack-representation-independence client =
  StackLogicalRelation .F-homᴰ client (tt* , tt*) tt*
