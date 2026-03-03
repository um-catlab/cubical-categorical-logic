{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc
module HyperDoc.CBPV.Model.Algebra where 

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma 
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor 
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)

open import HyperDoc.Algebra.Algebra hiding (Model)
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.CBPV.TypeStructure

open Alg
open AlgHom
open Category
open CBPVModel
open Functor
open NatTrans
open PshIso
open PshHom

module Model (Σ : Signature) where 
  AlgModel : CBPVModel Σ
  AlgModel .V = SET _
  AlgModel .C = ALG Σ
  AlgModel .O .F-ob (A , B) .Carrier = (SET _)[ A , B .Carrier ] , (SET _) .isSetHom
  AlgModel .O .F-ob (A , B) .interp op args = λ z → B .interp op (λ z₁ → args z₁ z)
  AlgModel .O .F-hom (f , h) .carmap g = λ z → h .carmap (g (f z))
  AlgModel .O .F-hom (f , h) .pres op args = funExt λ a → h .pres op λ z₁ → args z₁ (f a)
  AlgModel .O .F-id = AlgHom≡ refl
  AlgModel .O .F-seq _ _ = AlgHom≡ refl

  open TypeStructure AlgModel 

  hasV𝟙  : HasV𝟙 
  hasV𝟙 .fst = Unit , isSetUnit
  hasV𝟙 .snd .trans .N-ob c x = tt
  hasV𝟙 .snd .trans .N-hom _ _ _ _  = refl
  hasV𝟙 .snd .nIso x .fst = λ _ _ → tt
  hasV𝟙 .snd .nIso x .snd .fst tt = refl
  hasV𝟙 .snd .nIso x .snd .snd a  = funExt λ x₁ i → tt

  hasUTy : HasUTy 
  hasUTy B .fst = FORGET .F-ob B
  hasUTy B .snd .trans .N-ob = λ c z → z
  hasUTy B .snd .trans .N-hom c c' f p = refl
  hasUTy B .snd .nIso A .fst x x₁ = x x₁
  hasUTy B .snd .nIso A .snd .fst b = refl
  hasUTy B .snd .nIso A .snd .snd a = refl

  hasFTy : HasFTy
  hasFTy A .fst = FREE .F-ob A
  hasFTy A .snd .trans .N-ob = λ c z z₁ → z .carmap (inc z₁)
  hasFTy A .snd .trans .N-hom c c' f p = refl
  hasFTy A .snd .nIso B .fst f = FreeAlgMorphism f
  hasFTy A .snd .nIso B .snd .fst b = refl
  hasFTy A .snd .nIso B .snd .snd a = FreeAlgMorphism! λ _ → refl
