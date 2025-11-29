{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.CBPV.Instances.Kleisli where 

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels 
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.CBPV.Base
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.Instances.FromCat 
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.ExtensionSystem 
  renaming (Kleisli to KleisliCat)
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf 
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt
open import  Cubical.Categories.WithFamilies.Simple.Instances.Sets
  renaming (SET to SETSCwF)

open Category
open CBPVModel
open Functor
open EnrichedCategory
open EnrichedFunctor
open NatTrans
open PshHom

module _ {ℓ : Level}(M : ExtensionSystem (SET ℓ)) where 

  open ExtensionSystemFor (M .snd)

  K : Category (ℓ-suc ℓ) ℓ 
  K = KleisliCat (SET ℓ) M

  E : EnrichedCategory (PshMon.𝓟Mon (SET ℓ) ℓ) (ℓ-suc ℓ)
  E = Cat→Enriched K

  private 
    𝓟[_,_] = PshMon.𝓟 (SET ℓ) ℓ .Hom[_,_]
    self[_,_] = (self (SET ℓ) ℓ) .Hom[_,_]
    E[_,_] = E .Hom[_,_]

  -- LiftF ∘F (K [-, B ])  : Functor (K ^op) Set 
  -- not forgetful functor either.. ?
  computations : E .ob → (self (SET ℓ) ℓ) .ob 
  computations B .F-ob Γ = 
    Lift (K [ Γ , B ]) , 
    isOfHLevelLift 2 (K .isSetHom {Γ}{B})
  computations B .F-hom γ (lift m) = lift (m ∘S γ)
  computations B .F-id = funExt λ  _ → refl
  computations B .F-seq _ _ = funExt λ _ → refl

  stacks : (B B' : ob E) → 𝓟[ E[ B , B' ] , self[ computations B , computations B' ] ]
  stacks B B' .N-ob Γ (lift k) .N-ob Δ (γ , lift m) = lift λ Δ∙ → bind (k (γ Δ∙ )) (m Δ∙)
  stacks B B' .N-ob Γ (lift k) .N-hom Δ Θ γ (δ , lift m)= refl
  stacks B B' .N-hom γ = 
    funExt λ _ → makePshHomPath (funExt λ _ → funExt λ _ → refl)

  cTm : EnrichedFunctor ((PshMon.𝓟Mon (SET ℓ) ℓ)) E (self (SET ℓ) ℓ) 
  cTm .F-ob = computations
  cTm .F-hom {B}{B'} = stacks B B' 
  cTm .F-id = 
    makeNatTransPath (funExt λ Γ → funExt λ _ → 
      makePshHomPath (funExt λ Δ → funExt λ {(γ , m) → 
        cong lift (funExt λ d → funExt⁻ bind-r _)}) )
  cTm .F-seq = 
    makeNatTransPath (funExt λ Γ → funExt λ k,k' → 
      makePshHomPath (funExt λ Δ → funExt λ {(γ , m) → 
        cong lift (funExt λ d → funExt⁻ bind-comp _)})) 

  Kleisli : CBPVModel _ _ _ _ _ _
  Kleisli .Scwf = SETSCwF ℓ
  Kleisli .Stacks = E
  Kleisli .CTm = cTm