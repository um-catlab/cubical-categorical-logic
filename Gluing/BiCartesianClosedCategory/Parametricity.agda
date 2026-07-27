module Gluing.BiCartesianClosedCategory.Parametricity where 

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

module _ where
  data OB : Type where
    X : OB

  data MOR : Type ℓ-zero where
    flip read : MOR

  open QuiverOver

  +×⇒QUIVER : +×⇒Quiver ℓ-zero ℓ-zero
  +×⇒QUIVER .+×⇒Quiver.ob = OB
  +×⇒QUIVER .+×⇒Quiver.Q .mor = MOR
  +×⇒QUIVER .+×⇒Quiver.Q .dom flip = ↑ X
  +×⇒QUIVER .+×⇒Quiver.Q .dom read = ↑ X
  +×⇒QUIVER .+×⇒Quiver.Q .cod flip = ↑ X
  +×⇒QUIVER .+×⇒Quiver.Q .cod read = ⊤ + ⊤ 

  private
    module FREEBICCC = BiCartesianClosedCategory (FreeBiCartesianClosedCategory +×⇒QUIVER)

  InterpBool : CartesianFunctor FREEBICCC.CC (SET _) 
  InterpBool = recCF +×⇒QUIVER SETBiCCC 
      (mkElimInterpᴰ (λ{X → Bool , isSetBool}) 
        λ {flip → not
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

  ReadRel : Σ Bool (λ _ → ℕ) → Type
  ReadRel (b , n) =
    (Σ[ y ∈ Σ (Lift ℓ-zero Unit) (λ _ → Lift ℓ-zero Unit) ]
      Σ[ _ ∈ ((inl (y .fst) , inl (y .snd)) ≡
       ((if b then inl tt* else inr tt*) , even n))
      ] Lift ℓ-zero Unit)
    ⊎
    (Σ[ y ∈ Σ (Lift ℓ-zero Unit) (λ _ → Lift ℓ-zero Unit) ]
      Σ[ _ ∈ ((inr (y .fst) , inr (y .snd)) ≡
       ((if b then inl tt* else inr tt*) , even n))
      ] Lift ℓ-zero Unit)

  readBase : ∀ n → ReadRel (evenb n , n)
  readBase n with even n
  ... | inl u = inl ((tt* , u) , refl , tt*)
  ... | inr u = inr ((tt* , u) , refl , tt*)

  readᴰ : ∀ x → evenb (x .snd) ≡ x .fst → ReadRel x
  readᴰ (b , n) p =
    subst (λ b' → ReadRel (b' , n)) p
      (readBase n)

  InterpNat : CartesianFunctor FREEBICCC.CC (SET _) 
  InterpNat = recCF +×⇒QUIVER SETBiCCC  
    (mkElimInterpᴰ (λ {X  → ℕ , isSetℕ }) λ {flip → suc
                                           ; read → even})
                                           
  InterpBoolNat' : CartesianFunctor FREEBICCC.CC ((SET _) ×C (SET _))
  InterpBoolNat' .fst = InterpBool .fst ,F InterpNat .fst
  InterpBoolNat' .snd c c' Γ =
    compEquiv
      (Σ-cong-equiv
        (_ , InterpBool .snd c c' (Γ .fst))
        (λ _ → _ , InterpNat .snd c c' (Γ .snd)))
      (isoToEquiv
        (iso
          (λ z → (z .fst .fst , z .snd .fst) ,
                 (z .fst .snd , z .snd .snd))
          (λ z → (z .fst .fst , z .snd .fst) ,
                 (z .fst .snd , z .snd .snd))
          (λ _ → refl)
          (λ _ → refl)))
      .snd

  InterpBoolNat :
    CartesianFunctor FREEBICCC.CC (SET _)
  InterpBoolNat = _∘CF_ {C = FREEBICCC.CC}
    {(SETCC {ℓ-zero} ×CC SETCC {ℓ-zero})} ×SetsCF InterpBoolNat'

  BoolNatRelationGenerators :
    LogicalRelationGenerators +×⇒QUIVER SETBiCCC EqSETᴰBCCCⱽ
      ×SetsCF InterpBool InterpNat
  BoolNatRelationGenerators =
    mkElimInterpᴰ
      (λ { X (b , n) →
        (evenb n ≡ b) , isProp→isSet (isSetBool _ _)
      })
      λ
        { flip → λ (b , n) p → evenb-suc n ∙ cong not p
        ; read → readᴰ
        }

  S :
    Section
      (pointwise +×⇒QUIVER SETBiCCC EqSETᴰBCCCⱽ
        ×SetsCF InterpBool InterpNat .fst)
      (SETᴰ ℓ-zero ℓ-zero)
  S =
    logicalRelation +×⇒QUIVER SETBiCCC EqSETᴰBCCCⱽ
      ×SetsCF InterpBool InterpNat BoolNatRelationGenerators
