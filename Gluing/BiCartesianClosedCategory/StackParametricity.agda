module Gluing.BiCartesianClosedCategory.StackParametricity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
import Cubical.Data.Empty as Empty
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.List.Properties
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma as Sigma hiding (_×_)
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Functions.FunExtEquiv using (funExtDep)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Forded
  as FreeBiCCC renaming ([_,_] to [_,+_])
open import Gluing.BiCartesianClosedCategory.BinaryLogicalRelation
open import Gluing.BiCartesianClosedCategory.IdentityExtension

open Functor
open Section

data OB : Type where
  stack : OB

private
  embedClosed : BiCCCExpr Empty.⊥ → BiCCCExpr OB
  embedClosed = recBiCCCExpr λ ()

data MOR : Type where
  emptyStack : MOR
  push : MOR
  pop : MOR

open QuiverOver

two : BiCCCExpr OB
two = ⊤ + ⊤

Two : Type
Two = Unit* {ℓ-zero} ⊎ Unit* {ℓ-zero}

encodeBool : Bool → Two
encodeBool true = inl tt*
encodeBool false = inr tt*

decodeBool : Two → Bool
decodeBool (inl _) = true
decodeBool (inr _) = false

StackQuiver : +×⇒Quiver ℓ-zero ℓ-zero
StackQuiver .+×⇒Quiver.ob = OB
StackQuiver .+×⇒Quiver.Q .mor = MOR
StackQuiver .+×⇒Quiver.Q .dom emptyStack = ⊤
StackQuiver .+×⇒Quiver.Q .cod emptyStack = ↑ stack
StackQuiver .+×⇒Quiver.Q .dom push = two × (↑ stack)
StackQuiver .+×⇒Quiver.Q .cod push = ↑ stack
StackQuiver .+×⇒Quiver.Q .dom pop = ↑ stack
StackQuiver .+×⇒Quiver.Q .cod pop = ⊤ + (two × (↑ stack))

private
  module FREE =
    BiCartesianClosedCategory
      (FreeBiCartesianClosedCategory StackQuiver)

headPop : List Bool →
  Unit* {ℓ-zero} ⊎ (Σ[ _ ∈ Two ] (List Bool))
headPop [] = inl tt*
headPop (b ∷ xs) = inr (encodeBool b , xs)

reversePoppedStack :
  Unit* {ℓ-zero} ⊎ (Σ[ _ ∈ Two ] (List Bool)) →
  Unit* ⊎ (Σ[ _ ∈ Two ] (List Bool))
reversePoppedStack (inl u) = inl u
reversePoppedStack (inr (b , xs)) = inr (b , rev xs)

reversePop : List Bool →
  Unit* ⊎ (Σ[ _ ∈ Two ] (List Bool))
reversePop ys = reversePoppedStack (headPop (rev ys))

HeadFirstInterpretation :
  Interpretation StackQuiver SETBiCCC EqSETᴰBCCCⱽ
HeadFirstInterpretation =
  FreeBiCCC.mkElimInterpᴰ
    (λ { stack → List Bool , isOfHLevelList 0 isSetBool })
    λ { emptyStack → λ _ → []
      ; push → λ (b , xs) → decodeBool b ∷ xs
      ; pop → headPop }

HeadFirst : CartesianFunctor FREE.CC (SET ℓ-zero)
HeadFirst =
  interpretation StackQuiver SETBiCCC EqSETᴰBCCCⱽ
    HeadFirstInterpretation

ReverseStoredInterpretation :
  Interpretation StackQuiver SETBiCCC EqSETᴰBCCCⱽ
ReverseStoredInterpretation =
  FreeBiCCC.mkElimInterpᴰ
    (λ { stack → List Bool , isOfHLevelList 0 isSetBool })
    λ { emptyStack → λ _ → []
      ; push → λ (b , xs) → xs ++ (decodeBool b ∷ [])
      ; pop → reversePop }

ReverseStored : CartesianFunctor FREE.CC (SET ℓ-zero)
ReverseStored =
  interpretation StackQuiver SETBiCCC EqSETᴰBCCCⱽ
    ReverseStoredInterpretation

StackRelationGenerators :
  LogicalRelationGenerators StackQuiver SETBiCCC EqSETᴰBCCCⱽ
    HeadFirstInterpretation ReverseStoredInterpretation
StackRelationGenerators =
  FreeBiCCC.mkElimInterpᴰ
    (λ { stack (xs , ys) →
           (xs ≡ rev ys) ,
           isProp→isSet
             (isOfHLevelList 0 isSetBool _ _) })
    λ
      { emptyStack → λ _ _ → refl
      ; push → λ
        { ((b , xs) , (c , ys)) (inl (u , p , _) , q) →
            cong₂ _∷_
              (cong decodeBool
                (cong fst (sym p) ∙
                 cong inl (isPropUnit* (u .fst) (u .snd)) ∙
                 cong snd p))
              q ∙
            sym (rev-snoc ys (decodeBool c))
        ; ((b , xs) , (c , ys)) (inr (u , p , _) , q) →
            cong₂ _∷_
              (cong decodeBool
                (cong fst (sym p) ∙
                 cong inr (isPropUnit* (u .fst) (u .snd)) ∙
                 cong snd p))
              q ∙
            sym (rev-snoc ys (decodeBool c))
        }
      ; pop → λ
        { ([] , ys) q →
            inl ((tt* , tt*) ,
              ΣPathP (refl ,
                cong (λ zs → reversePoppedStack (headPop zs)) q) ,
              tt*)
        ; ((true ∷ xs) , ys) q →
            inr (((encodeBool true , xs) , (encodeBool true , rev xs)) ,
              ΣPathP (refl ,
                cong (λ zs → reversePoppedStack (headPop zs)) q) ,
              inl ((tt* , tt*) , refl , tt*) ,
              sym (rev-rev xs))
        ; ((false ∷ xs) , ys) q →
            inr (((encodeBool false , xs) , (encodeBool false , rev xs)) ,
              ΣPathP (refl ,
                cong (λ zs → reversePoppedStack (headPop zs)) q) ,
              inr ((tt* , tt*) , refl , tt*) ,
              sym (rev-rev xs))
        }
      }

StackLogicalRelation =
  logicalRelation StackQuiver SETBiCCC EqSETᴰBCCCⱽ
    HeadFirstInterpretation ReverseStoredInterpretation
    StackRelationGenerators

infix 4 _≈_
_≈_ : ∀ {A : BiCCCExpr Empty.⊥} →
  HeadFirst .fst .F-ob (embedClosed A) .fst →
  ReverseStored .fst .F-ob (embedClosed A) .fst →
  Type
_≈_ {A = A} x y =
  PathP
    (λ i →
      closedInterpretation≡ StackQuiver
        HeadFirstInterpretation ReverseStoredInterpretation
        StackRelationGenerators A i)
    x y

stack-representation-independence :
  (A B : BiCCCExpr Empty.⊥)
    (client : FREE.C [ embedClosed A , embedClosed B ]) →
  _≈_ {A = A ⇒ B}
    (HeadFirst .fst .F-hom client)
    (ReverseStored .fst .F-hom client)
stack-representation-independence A B client =
  funExtDep λ {x} {y} p →
    identityExtensionHom StackQuiver
      HeadFirstInterpretation ReverseStoredInterpretation
      StackRelationGenerators A B client x y p
