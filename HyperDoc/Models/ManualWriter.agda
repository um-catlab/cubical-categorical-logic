module HyperDoc.Models.ManualWriter where 


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
open import HyperDoc.CBPVLogic
open import HyperDoc.Syntax
open import HyperDoc.Logics.WriterMonadAlg
open import HyperDoc.Lib
open import HyperDoc.Effects.ManualWriter

open Algebra
open AlgebraHom
open Category
open Functor
open Model
open Logic

module _ 
  {ℓS  ℓP ℓP' : Level}
  {M : hSet ℓS} where

  open Writer M

  U : Functor (WRITERALG ℓS) (SET ℓS) 
  U .F-ob A = (A .fst .fst) , (A .snd)
  U .F-hom f = f .fst
  U .F-id = refl
  U .F-seq _ _ = refl

  F : Functor (SET ℓS) (WRITERALG ℓS) 
  F .F-ob X = FreeWriterAlg ⟨ X ⟩ , {!   !}
  F .F-hom {X}{Y} f = ext (FreeWriterAlg ⟨ Y ⟩) λ x → ret (f x)
  F .F-id = WriterHom≡ {!   !} {! refl  !} -- up
  F .F-seq = {!   !}

  CBPVWrite : Model  (ℓ-suc ℓS) ℓS (ℓ-suc ℓS) ℓS ℓS
  CBPVWrite .V = SET ℓS
  CBPVWrite .C = WRITERALG ℓS
  CBPVWrite .O .F-ob (A , B) = (SET ℓS) [ A , U .F-ob B ] , isSetHom (SET ℓS) {A}{U .F-ob B} 
  CBPVWrite .O .F-hom (f , g) h x = g .fst (h (f x)) 
  CBPVWrite .O .F-id = refl
  CBPVWrite .O .F-seq _ _ = refl

