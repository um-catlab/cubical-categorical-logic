{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.Model where 

open import Cubical.Data.FinData 

open import Cubical.Data.Sigma 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Functor 
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct

open import HyperDoc.Algebra.Algebra
open import HyperDoc.Operational.Effects.AlgGraph

open Category 
open Signature
open AlgGraph

CBPVModel : Signature → Type _
CBPVModel Sig  = 
  Σ[ V ∈ Category _ _ ] 
  Σ[ C ∈ Category _ _ ] 
  BifunctorSep (V ^op) C (ALGGRAPH Sig)

module CBPVModelSyntax 
  {Sig : Signature}
  (M : CBPVModel Sig) where 

  V = M .fst 
  C = M .snd .fst 
  O = M .snd .snd
  open BifunctorSep

  OPar = BifunctorToParFunctor (mkBifunctorSep O)

  O[_,_] : ob V → ob C → ob (ALGGRAPH Sig ) 
  O[_,_] A B = O .Bif-ob A  B

  O[-,_] : ob C → Functor (V ^op) (ALGGRAPH Sig) 
  O[-,_] = appR (mkBifunctorSep O)

  O[_,-] : ob V → Functor C (ALGGRAPH Sig) 
  O[_,-] = appL (mkBifunctorSep O)

  O'[_,_] : ob V → ob C → Type _
  O'[_,_] A B = O[ A , B ]  .fst .fst

  Node[_,_] : ob V → ob C → Type _
  Node[_,_] =  O'[_,_]

  Edge[_,_] : {A : ob V}{B : ob C} → (M M' : O'[ A , B ]) → Type _ 
  Edge[_,_] {A}{B} M M' = O[ A , B ] .snd .fst M M' .fst

  interp : {A : ob V}{B : ob C} → (op : Op Sig) → (Fin (arity Sig op) → Node[ A , B ]) → Node[ A , B ] 
  interp {A}{B} = O[ A , B ] .snd .snd


CBPVMorphism : 
  {Sig : Signature}
  (M N : CBPVModel Sig) → Type _
CBPVMorphism M N = 
  Σ[ Fv ∈ Functor M.V N.V ] 
  Σ[ Fc ∈ Functor M.C N.C ] 
  NatTrans M.OPar (N.OPar ∘F ((Fv ^opF) ×F Fc)) where 

  module M = CBPVModelSyntax M 
  module N = CBPVModelSyntax N

idModelMorphsim : 
  {Sig : Signature}
  (M : CBPVModel Sig ) →  
  CBPVMorphism M M 
idModelMorphsim M .fst = Id
idModelMorphsim M .snd .fst = Id
idModelMorphsim M .snd .snd .NatTrans.N-ob (A , B) .fst = λ z → z
idModelMorphsim M .snd .snd .NatTrans.N-ob (A , B) .snd .fst = λ z → z
idModelMorphsim M .snd .snd .NatTrans.N-ob (A , B) .snd .snd _ _ = refl
  -- (λ z → z) , (λ {n} {n'} z → z)
idModelMorphsim M .snd .snd .NatTrans.N-hom (V , S)= ΣPathP (refl , (ΣPathP (refl , {!   !})))

module CBPVMorphismSyntax 
   {Sig : Signature}
  {M N : CBPVModel Sig}
  (F : CBPVMorphism M N ) where

  FV = F .fst 
  FC = F .snd .fst 
  FO = F .snd .snd 