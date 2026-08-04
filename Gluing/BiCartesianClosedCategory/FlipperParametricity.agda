module Gluing.BiCartesianClosedCategory.FlipperParametricity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma as Sigma hiding (_×_)
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Forded as FreeBiCCC
  renaming ([_,_] to [_,+_])
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Gluing.BiCartesianClosedCategory.BinaryLogicalRelation
open import Gluing.BiCartesianClosedCategory.IdentityExtension

open Functor
open Section

module _ where
  data OB : Type where
    X : OB

  data MOR : Type ℓ-zero where
    init flip read : MOR

  open QuiverOver

  FlipperQuiver : +×⇒Quiver ℓ-zero ℓ-zero
  FlipperQuiver .+×⇒Quiver.ob = OB
  FlipperQuiver .+×⇒Quiver.Q .mor = MOR
  FlipperQuiver .+×⇒Quiver.Q .dom init = ⊤
  FlipperQuiver .+×⇒Quiver.Q .cod init = ↑ X
  FlipperQuiver .+×⇒Quiver.Q .dom flip = ↑ X
  FlipperQuiver .+×⇒Quiver.Q .cod flip = ↑ X
  FlipperQuiver .+×⇒Quiver.Q .dom read = ↑ X
  FlipperQuiver .+×⇒Quiver.Q .cod read = ⊤ + ⊤

  private
    module FREE =
      BiCartesianClosedCategory
        (FreeBiCartesianClosedCategory FlipperQuiver)

  InterpBoolData :
    Interpretation FlipperQuiver SETBiCCC EqSETᴰBCCCⱽ
  InterpBoolData =
    FreeBiCCC.mkElimInterpᴰ (λ{X → Bool , isSetBool})
        λ {init → λ _ → true
         ; flip → not
         ; read → if_then inl _ else inr _}

  InterpBool : CartesianFunctor FREE.CC (SET _)
  InterpBool =
    interpretation FlipperQuiver SETBiCCC EqSETᴰBCCCⱽ
      InterpBoolData

  even : ℕ → Lift ℓ-zero Unit ⊎ Lift ℓ-zero Unit
  even zero = inl _
  even (suc z) = Sum.rec inr inl (even z)

  evenb : ℕ → Bool
  evenb n = Sum.rec (λ _ → true) (λ _ → false) (even n)

  evenb-suc : ∀ n → evenb (suc n) ≡ not (evenb n)
  evenb-suc n with even n
  ... | inl _ = refl
  ... | inr _ = refl

  InterpNatData :
    Interpretation FlipperQuiver SETBiCCC EqSETᴰBCCCⱽ
  InterpNatData =
    FreeBiCCC.mkElimInterpᴰ
      (λ {X  → ℕ , isSetℕ })
      λ {init → λ _ → zero
        ; flip → suc
        ; read → even}

  InterpNat : CartesianFunctor FREE.CC (SET _)
  InterpNat =
    interpretation FlipperQuiver SETBiCCC EqSETᴰBCCCⱽ
      InterpNatData

  BoolNatRelationGenerators :
    LogicalRelationGenerators FlipperQuiver SETBiCCC EqSETᴰBCCCⱽ
      InterpBoolData InterpNatData
  BoolNatRelationGenerators .FreeBiCCC.ElimInterpᴰ.ı-ob X (b , n) =
    (evenb n ≡ b) , isProp→isSet (isSetBool _ _)
  BoolNatRelationGenerators .FreeBiCCC.ElimInterpᴰ.ı-hom init _ _ =
    refl
  BoolNatRelationGenerators .FreeBiCCC.ElimInterpᴰ.ı-hom flip (b , n) p =
    evenb-suc n ∙ cong not p
  BoolNatRelationGenerators .FreeBiCCC.ElimInterpᴰ.ı-hom
    read (b , n) p with even n
  ... | inl u =
    inl ((tt* , u) ,
      cong (λ b' → (if b' then inl tt* else inr tt*) , inl u) p ,
      tt*)
  ... | inr u =
    inr ((tt* , u) ,
      cong (λ b' → (if b' then inl tt* else inr tt*) , inr u) p ,
      tt*)

  FlipperLogicalRelation =
    logicalRelation FlipperQuiver SETBiCCC EqSETᴰBCCCⱽ
      InterpBoolData InterpNatData BoolNatRelationGenerators

  infix 4 _≈[_]_
  _≈[_]_ : ∀ {A} →
    InterpBool .fst .F-ob A .fst →
    BaseFree A →
    InterpNat .fst .F-ob A .fst →
    Type
  x ≈[ free ] y =
    PathP
      (λ i →
        baseFreeInterpretation≡ FlipperQuiver
          InterpBoolData InterpNatData BoolNatRelationGenerators free i)
      x y

  flipper-representation-independence :
    ∀ {A B} (freeA : BaseFree A) (freeB : BaseFree B)
      (client : FREE.C [ A , B ])
      (x : InterpBool .fst .F-ob A .fst)
      (y : InterpNat .fst .F-ob A .fst) →
    x ≈[ freeA ] y →
    InterpBool .fst .F-hom client x ≈[ freeB ]
      InterpNat .fst .F-hom client y
  flipper-representation-independence freeA freeB client x y =
    identityExtensionHom FlipperQuiver
      InterpBoolData InterpNatData BoolNatRelationGenerators
      freeA freeB client x y
