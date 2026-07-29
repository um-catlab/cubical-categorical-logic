module Gluing.BiCartesianClosedCategory.FlipperParametricity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure hiding (⟨_⟩)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum.Properties
open import Cubical.Data.Unit
open import Cubical.Data.Sigma as Sigma hiding (_×_)
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Quiver.Base
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import  Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.BinProduct.Cartesian
  renaming (_×_ to _×CC_)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Instances.Sets.Cartesian
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Instances.Weaken.UncurriedProperties
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Forded as FreeBiCCC
  renaming ([_,_] to [_,+_])
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Gluing.BiCartesianClosedCategory.BinaryLogicalRelation

open Functor
open Section

module _ where
  data OB : Type where
    X : OB

  data MOR : Type ℓ-zero where
    init flip read : MOR

  open QuiverOver

  +×⇒QUIVER : +×⇒Quiver ℓ-zero ℓ-zero
  +×⇒QUIVER .+×⇒Quiver.ob = OB
  +×⇒QUIVER .+×⇒Quiver.Q .mor = MOR
  +×⇒QUIVER .+×⇒Quiver.Q .dom init = ⊤
  +×⇒QUIVER .+×⇒Quiver.Q .dom flip = ↑ X
  +×⇒QUIVER .+×⇒Quiver.Q .dom read = ↑ X
  +×⇒QUIVER .+×⇒Quiver.Q .cod init = ↑ X
  +×⇒QUIVER .+×⇒Quiver.Q .cod flip = ↑ X
  +×⇒QUIVER .+×⇒Quiver.Q .cod read = ⊤ + ⊤ 

  private
    module FREEBICCC = BiCartesianClosedCategory (FreeBiCartesianClosedCategory +×⇒QUIVER)

  InterpBool : CartesianFunctor FREEBICCC.CC (SET _) 
  InterpBool = recCF +×⇒QUIVER SETBiCCC 
      (mkElimInterpᴰ (λ{X → Bool , isSetBool}) 
        λ {init → λ _ → true
         ; flip → not
         ; read → if_then inl _ else inr _})

  even : ℕ → Lift ℓ-zero Unit ⊎ Lift ℓ-zero Unit 
  even zero = inl _
  even (suc z) = Sum.rec inr inl (even z)

  evenb : ℕ → Bool 
  evenb n = Sum.rec (λ _ → true) (λ _ → false) (even n)

  evenb-suc : ∀ n → evenb (suc n) ≡ not (evenb n)
  evenb-suc n with even n
  ... | inl _ = refl
  ... | inr _ = refl

  InterpNat : CartesianFunctor FREEBICCC.CC (SET _) 
  InterpNat = recCF +×⇒QUIVER SETBiCCC  
    (mkElimInterpᴰ (λ {X  → ℕ , isSetℕ }) λ {init → λ _ → zero
                                           ; flip → suc
                                           ; read → even})
                                           
  BoolNatRelationGenerators :
    LogicalRelationGenerators +×⇒QUIVER SETBiCCC EqSETᴰBCCCⱽ
      ×SetsCF InterpBool InterpNat
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

  S :
    Section
      (pointwise +×⇒QUIVER SETBiCCC EqSETᴰBCCCⱽ
        ×SetsCF InterpBool InterpNat .fst)
      (SETᴰ ℓ-zero ℓ-zero)
  S =
    logicalRelation +×⇒QUIVER SETBiCCC EqSETᴰBCCCⱽ
      ×SetsCF InterpBool InterpNat BoolNatRelationGenerators

  flipper-representation-independence :
    (client : FREEBICCC.C [ ⊤ , ⊤ + ⊤ ]) →
      InterpBool .fst .F-hom client tt* ≡
      InterpNat .fst .F-hom client tt*
  flipper-representation-independence client
    with S .F-homᴰ client (tt* , tt*) tt*
  ... | inl (y , p , _) =
    cong fst (sym p) ∙
    cong inl (isPropUnit* (y .fst) (y .snd)) ∙
    cong snd p
  ... | inr (y , p , _) =
    cong fst (sym p) ∙
    cong inr (isPropUnit* (y .fst) (y .snd)) ∙
    cong snd p
