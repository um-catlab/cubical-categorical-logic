{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.Model where 

open import Cubical.Data.FinData 

open import Cubical.Data.Sigma 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Functor 
open import Cubical.Categories.Displayed.Functor 

open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base

open import HyperDoc.Algebra.Algebra
open import HyperDoc.Operational.Effects.BiAlgebra

open Alg renaming (interp to alginterp)
open Category 
open Categoryᴰ
open BiAlg renaming (Edge[_,_] to bEdge[_,_])
open Signature

CBPVModel : Signature → Type _
CBPVModel Sig  = 
  Σ[ V ∈ Category _ _ ] 
  Σ[ C ∈ Category _ _ ] 
  BifunctorSep (V ^op) C (BIALG Sig)

module CBPVModelSyntax 
  {Sig : Signature}
  (M : CBPVModel Sig) where 

  V = M .fst 
  C = M .snd .fst 
  O = M .snd .snd
  open BifunctorSep

  OPar = BifunctorToParFunctor (mkBifunctorSep O)

  O[_,_] : ob V → ob C → ob (BIALG Sig ) 
  O[_,_] A B = O .Bif-ob A  B

  O[-,_] : ob C → Functor (V ^op) (BIALG Sig) 
  O[-,_] = appR (mkBifunctorSep O)

  O[_,-] : ob V → Functor C (BIALG Sig) 
  O[_,-] = appL (mkBifunctorSep O)

  O'[_,_] : ob V → ob C → Type _
  O'[_,_] A B = O[ A , B ] .car .fst

  Node[_,_] : ob V → ob C → Type _
  Node[_,_] =  O'[_,_]

  Edge[_,_] : {A : ob V}{B : ob C} → (M M' : O'[ A , B ]) → Type _ 
  Edge[_,_] {A}{B} M M' = bEdge[_,_] O[ A , B ] M M'

  interp : {A : ob V}{B : ob C} → (op : Op Sig) → (Fin (arity Sig op) → Node[ A , B ]) → Node[ A , B ] 
  interp {A}{B} = O[ A , B ] .isAlg

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
idModelMorphsim M .snd .snd .NatTrans.N-ob (A , B) = idBHom
idModelMorphsim M .snd .snd .NatTrans.N-hom (V , S) = BiAlgHom≡ refl 

module CBPVMorphismSyntax 
   {Sig : Signature}
  {M N : CBPVModel Sig}
  (F : CBPVMorphism M N ) where

  FV = F .fst 
  FC = F .snd .fst 
  FO = F .snd .snd 
  



module _ 
  {Sig : Signature}
  (M : CBPVModel Sig)
   where

  open CBPVModelSyntax M

  CBPVModelᴰ : Type _ 
  CBPVModelᴰ = 
    Σ[ Vᴰ ∈ Categoryᴰ  V _ _ ]
    Σ[ Cᴰ ∈ Categoryᴰ C _ _ ]  
    BifunctorSepᴰ (M .snd .snd) (Vᴰ ^opᴰ) Cᴰ (BIALGᴰ {Sig})

module CBPVModelᴰSyntax 
  {Sig : Signature}
  {M : CBPVModel Sig}
  (Mᴰ : CBPVModelᴰ M) where 

  open CBPVModelSyntax M
  open BifunctorSepᴰ (Mᴰ .snd .snd)
  open BiAlgᴰ renaming (Edgeᴰ[_][_,_] to Edgeᴰ'[_][_,_])

  Vᴰ = Mᴰ .fst 
  Cᴰ = Mᴰ .snd .fst 
  Oᴰ = Mᴰ .snd .snd 

  --OᴰBif : Bifunctorᴰ (ParFunctorToBifunctor O) (Vᴰ ^opᴰ) Cᴰ ?
  --OᴰBif = ParFunctorᴰToBifunctorᴰ Oᴰ

  -- _⟪_⟫l
  -- Oᴰ'[ subC V M ][ vty A , cty B ]

  Oᴰ'[_][_,_] : {A : ob V}{B : ob C} → (O'[ A , B ])→ (Vᴰ .ob[_] A) → (Cᴰ .ob[_] B) → Type _ 
  Oᴰ'[_][_,_] {A}{B}M Aᴰ Bᴰ = Bif-obᴰ Aᴰ Bᴰ .carᴰ M .fst

  O[-][-,_] : {B : ob C} → Cᴰ .ob[_] B → Functorᴰ (appR (mkBifunctorSep O) B) (Vᴰ ^opᴰ)(BIALGᴰ {Sig})
  O[-][-,_] = appRᴰ (BifunctorSepᴰ→Bifunctorᴰ Oᴰ) 

  O[-][_,-] : {A : ob V} → Vᴰ .ob[_] A → Functorᴰ (appL (mkBifunctorSep O) A) (Cᴰ)((BIALGᴰ {Sig}))
  O[-][_,-] = appLᴰ (BifunctorSepᴰ→Bifunctorᴰ Oᴰ) 

  Nodeᴰ[_][_,_] : {A : ob V}{B : ob C} → (O'[ A , B ])→ (Vᴰ .ob[_] A) → (Cᴰ .ob[_] B) → Type _ 
  Nodeᴰ[_][_,_] = Oᴰ'[_][_,_]

  Edgeᴰ[_][_,_] : {A : ob V}{B : ob C}{Aᴰ : Vᴰ .ob[_] A}{Bᴰ : Cᴰ .ob[_] B}{M M' : O'[ A , B ]} →  
    (e :  Edge[ M , M' ] ) → Oᴰ'[ M ][ Aᴰ , Bᴰ ] → Oᴰ'[ M' ][ Aᴰ , Bᴰ ] → Type _ 
  Edgeᴰ[_][_,_] {Aᴰ = Aᴰ}{Bᴰ} = Edgeᴰ'[_][_,_] (Bif-obᴰ Aᴰ Bᴰ)
