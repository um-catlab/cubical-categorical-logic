{-# OPTIONS --allow-unsolved-metas #-}

module HyperDoc.Logics.WriterMonadAlg where

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base 
open import Cubical.Data.Sigma 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 
open import Cubical.Foundations.Powerset

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.ExtensionSystem hiding (F ; push)
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Instances.EilenbergMoore
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Instances.Preorders.Monotone hiding (_≤X_ ; _≤Y_)

open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties

open import Cubical.Relation.Binary.Preorder
 
open import HyperDoc.Effects.Writer

open Category
open ExtensionSystemFor
open Functor
open PreorderStr
open IsPreorder
open MonFun
open AlgebraHom
open IsEMAlgebra
-- specialized to some monoid on SET
module _ {ℓS : Level}{M : Monoid ℓS} where

  open MonoidStr (M .snd)
  
  open Writer {M = M}


  module _ (Alg : ob EM) where 
    open Algebra (Alg .fst) renaming (str to α)

    private 
      A : hSet ℓS
      A = carrier

    sub : ℙ ⟨ A ⟩ → hSet ℓS 
    sub P = (Σ[ a ∈ ⟨ A ⟩ ] ⟨ P a ⟩) , (isSetΣ (A .snd) λ a → isProp→isSet (P a .snd))

    closure : ℙ ⟨ A ⟩ → Type ℓS 
    closure P = (s : ⟨ F .F-ob (sub P) ⟩ ) → ⟨ P (α (F .F-hom {sub P}{carrier} fst s)) ⟩

    isPropclosure : (P : ℙ ⟨ A ⟩) → isProp (closure P) 
    isPropclosure P x y = funExt λ p  → P (α (F .F-hom {sub P}{carrier} (λ r → fst r) p)) .snd (x p) (y p)

    subAlg : Type (ℓ-suc ℓS) 
    subAlg = Σ[ P ∈ ℙ ⟨ A ⟩ ] closure  P


  subAlgPo : ob EM → ob (POSET (ℓ-suc ℓS) ℓS) 
  subAlgPo A .fst .fst = subAlg A
  subAlgPo A .fst .snd ._≤_ P Q = P .fst ⊆ Q .fst 
  subAlgPo A .fst .snd .isPreorder .is-prop-valued P Q = ⊆-isProp (P .fst)(Q .fst)
  subAlgPo A .fst .snd .isPreorder .is-refl P = ⊆-refl (P .fst)
  subAlgPo A .fst .snd .isPreorder .is-trans P Q R = ⊆-trans (P .fst) (Q .fst) (R .fst)
  -- this follows from antisym in ℙ
  subAlgPo A .snd = {!   !}

  open Algebra renaming (str to α)
  -- pushforward, op-cartesian lift
  module _ 
    {A B : ob EM} 
    (f : EM [ A , B ])
    (P : subAlg A )  where 

  
    Closed' : ⟨ B .fst .carrier ⟩ → Type ℓS 
    Closed' b = 
      Σ[ a ∈ ⟨ A .fst .carrier ⟩ ] 
      Σ[ w ∈ M .fst ] 
        ⟨ P .fst a ⟩ × (b ≡ B .fst .α (w , (f .carrierHom a)))

    Closed : ⟨ B .fst .carrier ⟩ → hProp ℓS 
    Closed b = ∥ Closed'  b ∥₁ , squash₁

    isClosed : closure B Closed
    isClosed (w , b , prf) = 
      rec squash₁ 
        (λ {(a , w' , Pa , b≡ ) → ∣ (a , w · w' , Pa , goal (a , w' , Pa , b≡ )) ∣₁}) 
        prf where 

        module _ ((a , w' , Pa , b≡ ) : Closed' b ) where

          f' = f .carrierHom

          have : b ≡ α (B .fst) (w' , f' a)
          have = b≡

          have' : α (B .fst) (w · w' , f' a) ≡ α (B .fst) (w · ε , (α (B .fst) (w' , (f' a)))) 
          have' = funExt⁻ (str-μ (B .snd)) (w , w' , f' a)

          goal : α (B .fst) (w · ε , b) ≡ α (B .fst) (w · w' , f .carrierHom a)
          goal = cong (λ h → α (B .fst) (w · ε , h)) have ∙ sym have'

  _◂_≤EM_ : (A : ob EM) → subAlg A → subAlg A → Type ℓS
  _◂_≤EM_ A = subAlgPo A .fst .snd ._≤_

  push : {A B : ob EM}(f : EM [ A , B ])→ subAlg A → subAlg B
  push {A}{B} f P = Closed {A}{B} f P , isClosed {A}{B} f P

  pushMono :  {A B : ob EM} (f : EM [ A , B ]){P Q : subAlg A} → 
    A ◂ P ≤EM Q → B ◂ push {A} {B} f P ≤EM push {A}{B} f Q
  pushMono = {! subAlgPo A .fst  !} 

  pushid : {A : ob EM} → push {A}{A}  (EM .id {A}) ≡ (POSET (ℓ-suc ℓS) ℓS) .id {subAlgPo A} .f
  pushid {A} = funExt λ x → 
    ΣPathP ((funExt (λ a → {! x  .fst a  !})) , 
      toPathP (isPropclosure A (x .fst) _ (snd x)))

  pushseq : {A B C : ob EM}(f : EM [ A , B ])(g : EM [ B , C ]) → 
    push {A}{C} ((EM ⋆ f) g) 
    ≡ 
    (POSET (ℓ-suc ℓS) ℓS) ._⋆_ {subAlgPo A}{subAlgPo B}{subAlgPo C} {!   !} {!   !} .MonFun.f
  pushseq = {! push ((EM ⋆ f) g) ≡
MonFun.f ((POSET (ℓ-suc ℓS) ℓS ⋆ ML .F-hom f) (ML .F-hom g))  !}

  -- notice that this is a covariant hyperdoctrine
  ML : Functor EM (POSET (ℓ-suc ℓS) ℓS) 
  ML .F-ob = subAlgPo
  ML .F-hom {A}{B} f .MonFun.f = push {A}{B} f
  ML .F-hom {A}{B} f .MonFun.isMon {P}{Q} = pushMono {A}{B} f  {P}{Q} 
  ML .F-id {A} = eqMon _ _ (pushid {A}) 
  ML .F-seq {x}{y}{z} f g = eqMon _ _ (funExt λ A' → ΣPathP ({!   !} , 
    (toPathP (isPropclosure z (Closed {x}{z} (EM ._⋆_  {x}{y}{z} f g) A')  _ _))))
  


