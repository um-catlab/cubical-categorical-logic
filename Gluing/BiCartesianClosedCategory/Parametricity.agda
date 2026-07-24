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
open import Cubical.Data.Quiver.Base
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import  Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Instances.Weaken.UncurriedProperties
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Forded as FreeBiCCC
  renaming ([_,_] to [_,+_])
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver

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

  even : ℕ → Lift ℓ-zero Unit  ⊎ Lift ℓ-zero Unit 
  even zero = inl _
  even (suc z) = Sum.rec inr inl (even z)

  InterpNat : CartesianFunctor FREEBICCC.CC (SET _) 
  InterpNat = recCF +×⇒QUIVER SETBiCCC  
    (mkElimInterpᴰ (λ {X  → ℕ , isSetℕ }) λ {flip → suc
                                           ; read → even})

  --InterpBoolNat : CartesianFunctor FREEBICCC.CC ((SET _) ×C (SET _)) 
 -- InterpBoolNat = (InterpBool ,F InterpNat) , {!   !}

  --×CF : CartesianFunctor {!  (SET _) × (SET _) !} ((SET _)) 
  --×CF = {!   !} , {!   !}  

 -- Interp

  InterpBoolNat : CartesianFunctor FREEBICCC.CC (SET _)
  InterpBoolNat = {!   !} -- comppose

  S : Section (InterpBoolNat .fst) (SETᴰ ℓ-zero ℓ-zero)
  S = FreeBiCCC.elimLocal +×⇒QUIVER InterpBoolNat EqSETᴰBCCCⱽ 
    (mkElimInterpᴰ (λ {X → λ (b , n ) → {! even n ≡ b  !}}) 
      -- [[ read ∘ flip]]_bool b ≡ [[ read ∘ flip ]]_nat n
      λ {flip → {!   !}
       ; read → {!   !}})

    



  







  
