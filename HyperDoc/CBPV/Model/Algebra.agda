{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc
module HyperDoc.CBPV.Model.Algebra where 

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma 

open import Cubical.Categories.Category
open import Cubical.Categories.Functor 
open import Cubical.Categories.Instances.Sets

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base

open Alg
open AlgHom
open Category
open CBPVModel
open Functor

AlgModel : (Σ : Signature) → CBPVModel Σ
AlgModel Σ .V = SET _
AlgModel Σ .C = ALG Σ
AlgModel Σ .O .F-ob (A , B) .Carrier = (SET _)[ A , B .Carrier ] , (SET _) .isSetHom
AlgModel Σ .O .F-ob (A , B) .interp op args = λ z → B .interp op (λ z₁ → args z₁ z)
AlgModel Σ .O .F-hom (f , h) .carmap g = λ z → h .carmap (g (f z))
AlgModel Σ .O .F-hom (f , h) .pres op args = funExt λ a → h .pres op λ z₁ → args z₁ (f a)
AlgModel Σ .O .F-id = AlgHom≡ refl
AlgModel Σ .O .F-seq _ _ = AlgHom≡ refl
