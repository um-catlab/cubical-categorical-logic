module HyperDoc.Models.Writer where

open import Cubical.Algebra.Monoid.Base

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure hiding(str)
open import Cubical.Functions.Logic
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.FunctorAlgebras 
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Posets.Base

open import HyperDoc.CBPVModel
open import HyperDoc.Logics.SetPred 
open import HyperDoc.Effects.Writer
open import HyperDoc.CBPVLogic
open import HyperDoc.Syntax
open import HyperDoc.Logics.WriterMonadAlg
open import HyperDoc.Lib

open Algebra
open AlgebraHom
open Category
open Functor
open Model
open CBPVLogic
open ORelFunctor 

module _ 
  {ℓS  ℓP ℓP' : Level}
  {M : Monoid ℓS} where 

  open Writer {M = M}
  
  CBPVWrite : Model  (ℓ-suc ℓS) ℓS (ℓ-suc ℓS) ℓS ℓS
  CBPVWrite .V = SET ℓS
  CBPVWrite .C = EM
  CBPVWrite .O .F-ob (A , B) = (SET ℓS) [ A , B .fst .carrier ] , isSetHom (SET ℓS) {A}{B .fst .carrier}
  CBPVWrite .O .F-hom (f , g) h x = g .carrierHom (h (f x))
  CBPVWrite .O .F-id = refl
  CBPVWrite .O .F-seq _ _ = refl 

  VL : Functor (SET ℓS ^op) (POSET (ℓ-suc ℓS) ℓS)
  VL = Pred {ℓS}{ℓP}{ℓP'}

  CL : Functor EM (POSET (ℓ-suc ℓS) ℓS) 
  CL = ML {ℓS}{M}

  module VL = HDSyntax VL
  module CL = HDSyntax {C = EM ^op} (CL ∘F from^op^op) 
  open import Cubical.HITs.PropositionalTruncation.Properties

  CBPVWriteLogic : CBPVLogic  CBPVWrite 
  CBPVWriteLogic .HL = VL
  CBPVWriteLogic .HC = CL
  CBPVWriteLogic .ORel .Rel {v}{c} P Q o = P ⊆ (Q .fst ∘S o) , ⊆-isProp P ((Q .fst ∘S o)) 
  CBPVWriteLogic .ORel .RelMono {v}{v'}{c}{c'}{o}{P}{P'}{Q}{Q'}{f}{g} VT CT OT x P'x = goal where 
    
    open MonoidStr (M .snd)
    open import Cubical.Categories.Monad.ExtensionSystem hiding (push)
    open ExtensionSystemFor (W' .snd)
    open import Cubical.Categories.Instances.EilenbergMoore
    open IsEMAlgebra
    open import Cubical.HITs.PropositionalTruncation.Base

    push' = push {M = M}{c}{c'}

    elem-c : ⟨ c .fst .carrier ⟩ 
    elem-c = o (f x)

    g' = g .carrierHom

    g⟨c⟩ : ⟨ c' . fst .carrier ⟩ 
    g⟨c⟩ = g' elem-c

    have : elem-c ∈ Q .fst 
    have = OT (f x) (VT x P'x)

    have' : g⟨c⟩ ∈ push' g Q .fst 
    have' = ∣ (elem-c , ε , have , sym (funExt⁻ (str-η (c' .snd)) (g' elem-c))) ∣₁


    mono : {!   !} 
    mono = {! pushMono {M = M}{c}{c'} g  !}

    lemma : c' CL.◂ push' g Q ≤ Q' 
    lemma x y = goal where 

      have'' : x ∈ push' g Q .fst
      have'' = y 

      goal : x ∈ Q' .fst 
      goal = 
        rec 
          (Q' .fst x .snd) 
          (λ{(q , r , s , t) → {! OT ? !}}) 
          y

    wrong : c' CL.◂ Q' ≤ push' g Q 
    wrong = CT

    goal : g⟨c⟩ ∈ Q' .fst
    goal = lemma g⟨c⟩ have'
{-
    have : x ∈ VL.f* f P
    have = VT x P'x

    have' : o (f x) ∈ Q .fst
    have' = OT (f x) have

    closedElem : Closed' {M = M} {c}{c'} g Q (g .carrierHom (o (f x))) 
    closedElem = (o (f x)) , (ε , (have' , sym (funExt⁻ (str-η (c' .snd)) (g .carrierHom (o (f x))))))

    inClosed : g .carrierHom (o (f x)) ∈ push {M = M}{c}{c'} g Q .fst
    inClosed = ∣ closedElem ∣₁

    _ : c' CL.◂ Q' ≤ push {M = M}{c}{c'} g Q 
    _ = CT
    mon : {!  pushMono {M = M} {c}{c'} g {Q}{Q} !}
    mon = pushMono {M = M} {c}{c'} g {Q}{Q}
    
    goal : (g .carrierHom (o (f x))) ∈ Q' .fst
    goal = {!   !}
    -- this works if we use the wrong variance in RelMono
    --goal = CT (g .carrierHom (o (f x))) inClosed

-}