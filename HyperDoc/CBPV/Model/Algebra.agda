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

open import HyperDoc.Algebra.Algebra renaming (Model to ModelDUH)
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

module Model' (T : Theory) where 
  open import Cubical.Categories.Constructions.BinProduct

  record CBPVModel' (T : Theory) : Type where 
    field 
      V : Category _ _ 
      C : Category _ _ 
      O : Functor ((V ^op) ×C C) (MOD T)
  open CBPVModel'
  open import Cubical.Data.Nat
  open import Cubical.Data.FinData
  open import Cubical.Foundations.Structure

  FunAlg : {Σ : Signature} → Type → Alg Σ → Alg Σ
  FunAlg A B .Carrier = (A → ⟨ B .Carrier ⟩) , {!   !}
  FunAlg A B .interp op args a = B .interp op (λ i → args i a)

  evalFun :
    {Σ : Signature}
    {A : Type}
    {B : Alg Σ}
    {n : ℕ}
    (t : Term Σ n)
    (env : (Fin n → (A → ⟨ B .Carrier ⟩)))
    (a : A)
    →
    eval (FunAlg A B) t env a
    ≡
    eval B t (λ i → env i a)
  evalFun (var x) γ a = refl
  evalFun {Σ}{A}{B}{n}(app o x) γ a i = 
    B .interp o λ z → evalFun{Σ}{A}{B}{n} (x z) γ  a i

  open Equation
  open Theory
  open ModelDUH
  AlgModel : CBPVModel' T
  AlgModel .V = SET _
  AlgModel .C = MOD T
  AlgModel .O .F-ob (A , B) .fst = FunAlg (A .fst) (B .fst)
  AlgModel .O .F-ob (A , B) .snd e env =
    funExt λ a → 
      evalFun (lhs (ax T e)) env a 
      ∙ B .snd e (λ i → env i a) 
      ∙ sym (evalFun (rhs (ax T e)) env a)

  AlgModel .O .F-hom (f , h) .carmap g a = h .carmap (g (f a))
  AlgModel .O .F-hom (f , h) .pres op args = funExt λ a → h .pres op λ x → args x (f a)
  AlgModel .O .F-id = AlgHom≡ refl
  AlgModel .O .F-seq _ _ = AlgHom≡ refl
module Model (Σ : Signature) where 
  AlgModel : CBPVModel Σ
  AlgModel .V = SET _
  AlgModel .C = ALG Σ
  AlgModel .O .F-ob (A , B) .Carrier = (SET _)[ A , B .Carrier ] , (SET _) .isSetHom
  AlgModel .O .F-ob (A , B) .interp op args = λ a → B .interp op (λ x → args x a)
  AlgModel .O .F-hom (f , h) .carmap g a = h .carmap (g (f a))
  AlgModel .O .F-hom (f , h) .pres op args = funExt λ a → h .pres op λ x → args x (f a)
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

  open import Cubical.Data.Sum
  hasO+ : HasO+ 
  hasO+ A A' .fst = (A .fst ⊎ A' .fst) , isSet⊎ (A .snd) (A' .snd)
  hasO+ A A' .snd .trans .N-ob (inl A'') = λ z → (λ z₁ → z (inl z₁)) , (λ z₁ → z (inr z₁))
  hasO+ A A' .snd .trans .N-ob (inr B) = λ z → (λ z₁ → z (inl z₁)) , (λ z₁ → z (inr z₁))
  hasO+ A A' .snd .trans .N-hom (inl x) (inl x₁) f p = refl
  hasO+ A A' .snd .trans .N-hom (inr x) (inl x₁) f p = refl
  hasO+ A A' .snd .trans .N-hom (inr x) (inr x₁) f p = refl
  hasO+ A A' .snd .nIso (inl x) .fst (f  , g) = rec f g
  hasO+ A A' .snd .nIso (inl x) .snd .fst b = refl
  hasO+ A A' .snd .nIso (inl x) .snd .snd f = funExt λ {(inl x) → refl
                                                      ; (inr x) → refl}
  hasO+ A A' .snd .nIso (inr x) .fst (f , g)= rec f g
  hasO+ A A' .snd .nIso (inr x) .snd .fst b = refl
  hasO+ A A' .snd .nIso (inr x) .snd .snd f = funExt λ {(inl x) → refl
                                                      ; (inr x) → refl}
