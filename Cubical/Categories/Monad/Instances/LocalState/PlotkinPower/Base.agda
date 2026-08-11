module Cubical.Categories.Monad.Instances.LocalState.PlotkinPower.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Properties

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Injections
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Limits.Coend
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions.Tensor

open Category
open Bifunctor
open Functor
open UniversalElement

module _ {ℓV : Level}(V : hSet ℓV) where

  Store : Functor (Inj ^op) (SET ℓV)
  Store .F-ob n = (Fin n → ⟨ V ⟩) , isSet→ (V .snd)
  Store .F-hom f s i = s (f .fst i)
  Store .F-id = refl
  Store .F-seq f g = refl

  Store+Iso : (n m : ℕ) →
    Iso (Fin (n + m) → ⟨ V ⟩)
        ((Fin n → ⟨ V ⟩) × (Fin m → ⟨ V ⟩))
  Store+Iso n m = equivToIso
    (compEquiv
      (preCompEquiv (FinSumChar.Equiv n m))
      Π⊎≃)

  splitStoreAlong : {n m : ℕ} (f : Injection n m) →
    (Fin m → ⟨ V ⟩) →
    (Fin n → ⟨ V ⟩) × (Fin (complementSize f) → ⟨ V ⟩)
  splitStoreAlong f Sm =
    Iso.fun Π⊎Iso
      (λ x → Sm (Iso.fun (finiteImageComplementIso f) x))

  module _ {ℓA} (A : Functor Inj (SET ℓA)) where

    Cov : (n : ℕ) → Functor Inj (SET ℓA)
    Cov n = ×Sets ∘F (A ,F (Inj [ n ,-]))

    Diagram : (n : ℕ) →
      Bifunctor (Inj ^op) Inj (SET (ℓ-max ℓV ℓA))
    Diagram n = ×SetsBif ∘Fl Store ∘Fr Cov n

    LocalStateAt : (n : ℕ) → hSet (ℓ-max ℓA ℓV)
    LocalStateAt n = ⊗-Bif ⟅ Cov n , Store ⟆b

    localStateCowedge : (n : ℕ) → Cowedge (Diagram n) (LocalStateAt n)
    localStateCowedge n .Cowedge.ψ p (s , a , f) =
      (a , f) ,⊗ s
      where open Tensor (Cov n) Store
    localStateCowedge n .Cowedge.extranatural h =
      funExt λ (s , a , f) → sym (swap (a , f) h s)
      where open Tensor (Cov n) Store

    localStateCoend : (n : ℕ) → Coend (Diagram n)
    localStateCoend n .vertex = LocalStateAt n
    localStateCoend n .element = localStateCowedge n
    localStateCoend n .universal X = isoToIsEquiv
      (iso to from
        (λ w → Cowedge≡ (Diagram n) (funExt λ p → funExt λ x → refl))
        (λ g →
          funExt (R.ind (λ x → (X .snd) _ _) λ (a , f) s → refl)))
      where
      module R = Tensor (Cov n) Store

      to : (LocalStateAt n .fst → X .fst) → Cowedge (Diagram n) X
      to g = (CoendPsh (Diagram n) .F-hom g) (localStateCowedge n)

      from : Cowedge (Diagram n) X → LocalStateAt n .fst → X .fst
      from w = R.rec (X .snd)
        (λ (a , f) s → w .Cowedge.ψ _ (s , a , f))
        (λ (a , f) h s →
          sym (funExt⁻ (w .Cowedge.extranatural h) (s , a , f)))

  [Inj,Set] : Category (ℓ-suc ℓV) ℓV
  [Inj,Set] = FUNCTOR Inj (SET ℓV)

  T : Functor [Inj,Set] [Inj,Set]
  T .F-ob A .F-ob n .fst =
    (Fin n → V .fst) → LocalStateAt A n .fst
  T .F-ob A .F-ob n .snd = isSet→ (LocalStateAt A n .snd)
  T .F-ob A .F-hom {n}{m} f t Sm = goal where 

    module Rₙ = Tensor (Cov A n) Store
    module Rₘ = Tensor (Cov A m) Store
    
    Sn : LocalStateAt A n .fst 
    Sn = t (Store .F-hom {m}{n} f Sm)

    ext : ℕ 
    ext = complementSize f

    goal : LocalStateAt A m .fst 
    goal = Rₙ.rec 
      (LocalStateAt A m .snd) 
      (λ { {p} (Ap , g) Sp  → 
        Rₘ._,⊗_ {p + ext} 
        (A .F-hom extendInjection Ap , 
        extendAlong f g )
        (Store+Iso p ext .Iso.inv (Sp , splitStoreAlong f Sm .snd)) }) 
      {!   !} 
      Sn 
  T .F-ob A .F-id = {!   !}
  T .F-ob A .F-seq = {!   !}
  T .F-hom = {!   !}
  T .F-id = {!   !}
  T .F-seq = {!   !}
