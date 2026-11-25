{-# OPTIONS --lossy-unification #-}
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
import Cubical.Data.Equality as Eq
open import Cubical.Functions.FunExtEquiv using (funExtDep)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Sets
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
  Interpretation StackQuiver SETBiCCC SETCodBCCCⱽ
HeadFirstInterpretation =
  FreeBiCCC.mkElimInterpᴰ
    (λ { stack → List Bool , isOfHLevelList 0 isSetBool })
    λ { emptyStack → λ _ → []
      ; push → λ (b , xs) → decodeBool b ∷ xs
      ; pop → headPop }

HeadFirst : CartesianFunctor FREE.CC (SET ℓ-zero)
HeadFirst =
  interpretation StackQuiver SETBiCCC SETCodBCCCⱽ
    HeadFirstInterpretation

ReverseStoredInterpretation :
  Interpretation StackQuiver SETBiCCC SETCodBCCCⱽ
ReverseStoredInterpretation =
  FreeBiCCC.mkElimInterpᴰ
    (λ { stack → List Bool , isOfHLevelList 0 isSetBool })
    λ { emptyStack → λ _ → []
      ; push → λ (b , xs) → xs ++ (decodeBool b ∷ [])
      ; pop → reversePop }

ReverseStored : CartesianFunctor FREE.CC (SET ℓ-zero)
ReverseStored =
  interpretation StackQuiver SETBiCCC SETCodBCCCⱽ
    ReverseStoredInterpretation

private
  sameTwo : ∀ {b c : Two} (u : Unit* {ℓ-zero} Sigma.× Unit* {ℓ-zero})
    → (b' : Unit* {ℓ-zero} → Two)
    → (b' (u .fst) , b' (u .snd)) ≡ (b , c) → b ≡ c
  sameTwo u b' p =
    cong fst (sym p) ∙ cong b' (isPropUnit* (u .fst) (u .snd)) ∙ cong snd p

  sameStack : ∀ {xs ys : List Bool} (w : List Bool Sigma.× List Bool)
    → w .fst ≡ rev (w .snd) → w ≡ (xs , ys) → xs ≡ rev ys
  sameStack w q0 p = sym (cong fst p) ∙ q0 ∙ cong (λ v → rev (v .snd)) p

  fst₂ : ∀ {A B C D : Type} → (A Sigma.× B) Sigma.× (C Sigma.× D) → A Sigma.× C
  fst₂ v = v .fst .fst , v .snd .fst

  snd₂ : ∀ {A B C D : Type} → (A Sigma.× B) Sigma.× (C Sigma.× D) → B Sigma.× D
  snd₂ v = v .fst .snd , v .snd .snd

  popPath : ∀ {xs ys} → xs ≡ rev ys
    → (headPop xs , reversePoppedStack (headPop xs))
      ≡ (headPop xs , reversePop ys)
  popPath q = ΣPathP (refl ,
    cong (λ zs → reversePoppedStack (headPop zs)) q)

StackRelationGenerators :
  LogicalRelationGenerators StackQuiver SETBiCCC SETCodBCCCⱽ
    HeadFirstInterpretation ReverseStoredInterpretation
StackRelationGenerators =
  FreeBiCCC.mkElimInterpᴰ
    (λ { stack (xs , ys) →
           (xs ≡ rev ys) ,
           isProp→isSet
             (isOfHLevelList 0 isSetBool _ _) })
    λ
      { emptyStack → mk ℓ-zero λ _ → (_ , refl) , refl
      ; push → mk ℓ-zero λ
        { (((b , xs) , (c , ys)) ,
            ((_ , (_ , inl ((u , _) , e)) , q') , q) ,
            ((_ , (w , q0) , p') , p)) →
            (_ , cong₂ _∷_
                (cong decodeBool (sameTwo u inl (e ∙ q' ∙ cong fst₂ q)))
                (sameStack w q0 (p' ∙ cong snd₂ p))
              ∙ sym (rev-snoc ys (decodeBool c)))
            , refl
        ; (((b , xs) , (c , ys)) ,
            ((_ , (_ , inr ((u , _) , e)) , q') , q) ,
            ((_ , (w , q0) , p') , p)) →
            (_ , cong₂ _∷_
                (cong decodeBool (sameTwo u inr (e ∙ q' ∙ cong fst₂ q)))
                (sameStack w q0 (p' ∙ cong snd₂ p))
              ∙ sym (rev-snoc ys (decodeBool c)))
            , refl
        }
      ; pop → mk ℓ-zero λ
        { (([] , ys) , q) →
            (_ , inl (((tt* , tt*) , tt*) , popPath q)) , refl
        ; (((true ∷ xs) , ys) , q) →
            (_ , inr ((((encodeBool true , xs) , (encodeBool true , rev xs)) ,
              ((_ , (_ , inl (((tt* , tt*) , tt*) , refl)) , refl) , refl) ,
              ((_ , (_ , sym (rev-rev xs)) , refl) , refl)) ,
              popPath q))
            , refl
        ; (((false ∷ xs) , ys) , q) →
            (_ , inr ((((encodeBool false , xs) , (encodeBool false , rev xs)) ,
              ((_ , (_ , inr (((tt* , tt*) , tt*) , refl)) , refl) , refl) ,
              ((_ , (_ , sym (rev-rev xs)) , refl) , refl)) ,
              popPath q))
            , refl
        }
      }

StackLogicalRelation =
  logicalRelation StackQuiver SETBiCCC SETCodBCCCⱽ
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

private
  module Examples where
    isInl : ∀ {ℓa ℓb} {X : Type ℓa} {Y : Type ℓb} → X ⊎ Y → Bool
    isInl (inl _) = true
    isInl (inr _) = false

    client : Expr StackQuiver ⊤ (⊤ + ⊤)
    client =
      ((⟨ !ₑ Eq.refl ⋆ₑ σ₁ Eq.refl Eq.refl , ↑ₑ StackQuiver emptyStack ⟩
          Eq.refl
        ⋆ₑ ↑ₑ StackQuiver push) ⋆ₑ ↑ₑ StackQuiver pop)
      ⋆ₑ [ !ₑ Eq.refl ⋆ₑ σ₂ Eq.refl Eq.refl ,+ π₁ Eq.refl Eq.refl ] Eq.refl

    _ : isInl
      (pt ℓ-zero (StackLogicalRelation .F-homᴰ client) ((tt* , tt*) , tt*)
        .fst .snd) ≡ true
    _ = refl

    _ : (i : I) → isInl
      (stack-representation-independence ⊤ (⊤ + ⊤) client i tt*) ≡ true
    _ = λ i → refl
