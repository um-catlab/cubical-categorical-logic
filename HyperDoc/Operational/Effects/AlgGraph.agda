{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.AlgGraph where 

open import Cubical.Data.Sigma
open import Cubical.Data.FinData

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets

open import HyperDoc.Algebra.Algebra hiding(FORGET)
open import HyperDoc.Operational.Graph hiding(FORGET)

open Category
open Signature
open Functor

module AlgGraph (Sig : Signature) where 


  AlgGraph : Type  {!   !}
  AlgGraph = 
    Σ[ Node ∈ hSet _ ] 
    Σ[ Edge ∈ (⟨ Node ⟩ → ⟨ Node ⟩ → hSet {!   !}) ] 
    ((op : Op Sig) → (Fin (arity Sig op) → ⟨ Node ⟩) → ⟨ Node ⟩)
    -- should interp be a graph homomorphism?
    -- then this is an algebra internal to the category of graphs

  asAlg : AlgGraph → Alg Sig 
  asAlg A = record { Carrier = A .fst ; interp = A .snd .snd }

  asGraph : AlgGraph → Graph _ _ 
  asGraph A = A .fst , A .snd .fst


  AlgGraphHom : AlgGraph → AlgGraph → Type {!   !} 
  AlgGraphHom X Y = 
    Σ[ f ∈ (⟨ X .fst ⟩ → ⟨ Y .fst ⟩) ] 
    isGraphHom {G = asGraph X}{asGraph Y} f 
    × 
    isAlgHom {Sig}{asAlg X}{asAlg Y} f

  ALGGRAPH : Category _ _ 
  ALGGRAPH .ob = AlgGraph
  ALGGRAPH .Hom[_,_] = AlgGraphHom
  ALGGRAPH .id = (λ z → z) , (λ {n} {n'} z → z) , λ op args → refl
  (ALGGRAPH ⋆ f) g .fst z = g .fst (f .fst z)
  (ALGGRAPH ⋆ f) g .snd .fst = λ z₁ → g .snd .fst (f .snd .fst z₁)
  (ALGGRAPH ⋆ f) g .snd .snd op args = cong (g .fst) (f .snd .snd  op args) ∙ g .snd .snd op (λ x₁ → f .fst (args x₁))
  ALGGRAPH .⋆IdL f = ΣPathP (refl , (ΣPathP (refl , {!  !})))
  ALGGRAPH .⋆IdR = {!   !}
  ALGGRAPH .⋆Assoc = {!   !}
  ALGGRAPH .isSetHom = {!   !}

  FORGET : Functor ALGGRAPH (SET _) 
  FORGET .F-ob = fst
  FORGET .F-hom = fst
  FORGET .F-id = refl
  FORGET .F-seq _ _ = refl


module AlgPre (Sig : Signature) where 
  open import Cubical.Categories.Instances.Preorders.Base
  open import Cubical.Categories.Instances.Preorders.Monotone
  open import Cubical.Relation.Binary.Preorder renaming (Preorder to Preorder')
  open MonFun renaming (f to fun)
  open PreorderStr
  open  IsPreorder

  Preorder = ob (PREORDER _ _)

  AlgPre : Type {!   !}
  AlgPre = 
    Σ[ P ∈ Preorder ] (((op : Op Sig) → (Fin (arity Sig op) → P .fst .fst ) → P .fst .fst))

  asAlg : AlgPre → Alg Sig 
  asAlg X .Alg.Carrier = X .fst .fst .fst  , X .fst .snd
  asAlg X .Alg.interp = X .snd

  AlgPreHom : AlgPre → AlgPre → Type {!   !}
  AlgPreHom X Y = Σ[ f ∈ (PREORDER _ _) [ X .fst , Y .fst ] ] isAlgHom {Sig}{asAlg  X}{asAlg Y} (fun f)


  ALGPRE : Category _ _
  ALGPRE .ob = AlgPre
  ALGPRE .Hom[_,_] = AlgPreHom
  ALGPRE .id .fst = record { f = λ z → z ; isMon = λ {x = x₁} {y} z → z }
  ALGPRE .id .snd op args = refl
  (ALGPRE ⋆ f) g .fst = record
    { f = λ z₁ → g .fst .fun (f .fst .fun z₁)
    ; isMon = λ {x = x₁} {y = y₁} z₁ → g .fst .isMon (f .fst .isMon z₁)
    }
  (ALGPRE ⋆ f) g .snd op args = {!   !}
  ALGPRE .⋆IdL = {!   !}
  ALGPRE .⋆IdR = {!   !}
  ALGPRE .⋆Assoc = {!   !}
  ALGPRE .isSetHom = {!   !} 


module RTC (Sig : Signature) where
  open AlgGraph Sig 
  open AlgPre Sig 
  open import Cubical.Categories.Instances.Preorders.Monotone

  hmm : ALGGRAPH .ob → ALGPRE .ob 
  hmm x .fst = graphToPre (asGraph x)
  hmm x .snd = x .snd .snd

  RTCAlgGraphF : Functor ALGGRAPH ALGPRE 
  RTCAlgGraphF .F-ob = hmm
  RTCAlgGraphF .F-hom f .fst = graphToPreHom (f .fst , f .snd .fst)
  RTCAlgGraphF .F-hom f .snd = f .snd .snd
  RTCAlgGraphF .F-id = ΣPathP (eqMon _ _ refl , {!refl   !})
  RTCAlgGraphF .F-seq = {!   !}