{-# OPTIONS --type-in-type #-}
-- TODO Separate this into multiple files
-- fix level issues
-- reorder imports, etc

module HyperDoc.Algebra.Algebra where

open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic

open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Cubical.Relation.Binary.Preorder

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base

open Category
open Categoryᴰ
open Functor
open PreorderStr


------------------------------------------------------------------------
-- 1. Signature (finite arity)

record Signature : Set₁ where
  field
    Op    : Set
    arity : Op → ℕ

open Signature

------------------------------------------------------------------------
-- 2. Terms in context of n variables

data Term (Σ : Signature) (n : ℕ) : Set where
  var : Fin n → Term Σ n

  app : (o : Op Σ)
      → (Fin (arity Σ o) → Term Σ n)
      → Term Σ n

------------------------------------------------------------------------
-- 3. Renaming

rename :
  {Σ : Signature} {n m : ℕ} →
  (Fin n → Fin m) →
  Term Σ n →
  Term Σ m
rename ρ (var i)      = var (ρ i)
rename ρ (app o args) =
  app o (λ j → rename ρ (args j))

------------------------------------------------------------------------
-- 4. Substitution

substT :
  {Σ : Signature} {n m : ℕ} →
  (Fin n → Term Σ m) →
  Term Σ n →
  Term Σ m
substT σ (var i)      = σ i
substT σ (app o args) =
  app o (λ j → substT σ (args j))

------------------------------------------------------------------------
-- 5. Equations (in context n)

record Equation (Σ : Signature) : Set₁ where
  field
    ctx : ℕ
    lhs : Term Σ ctx
    rhs : Term Σ ctx

------------------------------------------------------------------------
-- 6. Theory = signature + equations

record Theory : Set₁ where
  field
    Sig   : Signature
    Eq  : Set
    ax  : Eq → Equation Sig

------------------------------------------------------------------------
-- 7. Algebras for a signature

record Alg (Σ : Signature) : Set₁ where
  field
    Carrier : hSet _
    interp  :
      (o : Op Σ) →
      (Fin (arity Σ o) → ⟨ Carrier ⟩) →
      ⟨ Carrier ⟩ 

open Alg


------------------------------------------------------------------------
-- 8. Interpretation of terms

eval :
  {Σ : Signature} →
  (A : Alg Σ) →
  {n : ℕ} →
  Term Σ n →
  (Fin n → ⟨ Carrier A ⟩ ) →
  ⟨ Carrier A ⟩ 
eval A (var i) ρ = ρ i
eval A (app o args) ρ =
  interp A o (λ j → eval A (args j) ρ)

------------------------------------------------------------------------
-- 9. Satisfaction of an equation

satisfies :
  {Σ : Signature} →
  (A : Alg Σ) →
  Equation Σ →
  Set
satisfies A e = 
  ∀ (ρ : Fin (Equation.ctx e) → ⟨ Carrier A ⟩ ) →
    eval A (Equation.lhs e) ρ
      ≡
    eval A (Equation.rhs e) ρ

------------------------------------------------------------------------
-- 10. Model of a theory

record Model (T : Theory) : Set₁ where
  field
    alg   : Alg (Theory.Sig T)
    sound :
      (e : Theory.Eq T) →
      satisfies alg (Theory.ax T e)


record AlgHom {Sig : Signature} (M N : Alg Sig) : Type where 
  field 
    carmap : ⟨ M .Carrier ⟩  → ⟨ N .Carrier ⟩ 
    pres : ∀ (op : Sig .Op)(args : Fin (Sig .arity op) → ⟨ M .Carrier ⟩ ) 
      → carmap (interp M op args) ≡ interp N op λ x → carmap (args x)

open AlgHom

isAlgHom : {Sig : Signature}{M N : Alg Sig}→  (⟨ M .Carrier ⟩  → ⟨ N .Carrier ⟩)  → Type 
isAlgHom {Sig} {M} {N} f = ∀ (op : Sig .Op)(args : Fin (Sig .arity op) → ⟨ M .Carrier ⟩ ) 
      → f (interp M op args) ≡ interp N op λ x → f (args x)

AlgHom≡ : {Sig : Signature}{M N : Alg Sig}{f g : AlgHom M N} → 
  f .carmap ≡ g .carmap → 
  f ≡ g
AlgHom≡ prf i .carmap = prf i
AlgHom≡ {f = f}{g} prf i .pres op args = {!   !}

idHom : {Sig : Signature} {M : Alg Sig} → AlgHom M M 
idHom .AlgHom.carmap x = x
idHom .AlgHom.pres op args = refl

_⋆AlgHom_ : {Sig : Signature}{M N P : Alg Sig} → AlgHom M N → AlgHom N P → AlgHom M P
(f ⋆AlgHom g) .AlgHom.carmap = λ z → g .AlgHom.carmap (f .AlgHom.carmap z)
(f ⋆AlgHom g) .AlgHom.pres op args = cong (λ h → g .carmap h ) (f .pres op args) ∙ g .pres op λ x → f .carmap (args x)

ALG : Signature → Category (ℓ-suc ℓ-zero) ℓ-zero 
ALG S .ob = Alg S
ALG S .Hom[_,_] = AlgHom
ALG S .id = idHom
ALG S ._⋆_ = _⋆AlgHom_
ALG S .⋆IdL _ = AlgHom≡ refl
ALG S .⋆IdR _ = AlgHom≡ refl
ALG S .⋆Assoc _ _ _ = AlgHom≡ refl
ALG S .isSetHom = {!   !}

Cong : {Σ : Signature}{A : Alg Σ} → ℙ ⟨ Carrier A ⟩  → Type 
Cong {Σ}{A} P = (op : Op Σ)(args : Fin (arity Σ op) → Σ[ a ∈ ⟨ Carrier A ⟩ ] a ∈ P ) → 
  interp A op (λ i → args i .fst) ∈ P

isPropCong : {Σ : Signature}{A : Alg Σ} → (P : ℙ ⟨ Carrier A ⟩) → isProp (Cong {Σ}{A} P) 
isPropCong {Σ}{A} P = 
  isPropΠ  λ op → 
  isPropΠ λ args → 
  ∈-isProp P (interp A op (λ i → args i .fst))

_⊃⊂_ : {X : Type} → (P Q :  ℙ X) → Type
_⊃⊂_ P Q = (P ⊆ Q) × (Q ⊆ P)

SubAlg : {Σ : Signature} → Alg Σ → Type
SubAlg {Σ} A = Σ[ P ∈ ℙ ⟨ Carrier A ⟩  ] (Cong {Σ}{A} P)

SubAlg≡ : {Σ : Signature}{A : Alg Σ}→ (P Q : SubAlg A) → (P .fst) ⊃⊂ (Q .fst) →  P ≡ Q
SubAlg≡ {Σ}{A} P Q prf = 
  ΣPathP (funExt (λ a → ⇔toPath (prf .fst a) (prf .snd a)) , 
  toPathP (isPropCong {Σ}{A} (Q .fst) _ _))

subAlgPo : {Σ : Signature} → ob (ALG Σ) → ob (POSET  _ _) 
subAlgPo A .fst .fst = SubAlg A
subAlgPo A .fst .snd ._≤_ P Q = P .fst ⊆ Q .fst
subAlgPo A .fst .snd .isPreorder .IsPreorder.is-prop-valued P Q = ⊆-isProp (P .fst)(Q .fst)
subAlgPo A .fst .snd .isPreorder .IsPreorder.is-refl P = ⊆-refl (P .fst)
subAlgPo A .fst .snd .isPreorder .IsPreorder.is-trans P Q R = ⊆-trans (P .fst) (Q .fst) (R .fst)
-- this follows from antisym in ℙ
subAlgPo A .snd = {!!}

AlgPred : (Σ : Signature) →  Functor ((ALG Σ) ^op) (POSET ℓ-zero ℓ-zero)
AlgPred Σ .F-ob = subAlgPo
AlgPred Σ .F-hom f .MonFun.f (P , clP) .fst a = P (f .carmap a)
AlgPred Σ .F-hom {B}{B'} f .MonFun.f (P , clP) .snd op args = goal where 
  have : f .carmap (interp B' op λ a → args a .fst) ≡ interp B op (λ a → f .carmap (args a .fst))
  have = f .pres op  λ a → args a .fst

  have' : interp B op (λ i → f .carmap (args i .fst)) ∈ P
  have' = clP  op λ z → f .carmap (args z .fst) , args z .snd

  goal : interp B' op (λ i → args i .fst) ∈ (λ a → P (f .carmap a))
  goal = subst (λ h → h ∈ P) (sym have) have'

AlgPred Σ .F-hom f .MonFun.isMon = λ z x₂ → z (f .carmap x₂)
AlgPred Σ .F-id {B} = 
  eqMon _ _ (funExt λ P → 
  SubAlg≡ {Σ}{B} 
    _ _ 
    ((λ x z → z) , λ x z → z))
AlgPred Σ .F-seq {B}{B'}{B''} f g = 
  eqMon _ _ (funExt λ P → 
  SubAlg≡ {Σ}{B''} _ _ 
  ((λ x z → z) , λ x z → z))

data FreeOn (S : Signature)(X : Type) : Type where 
  inc : X → FreeOn S X
  ops : (o : Op S) → (Fin (arity S o) → FreeOn S X) → FreeOn S X

FreeAlg : (Σ : Signature)(X : Type) → Alg Σ 
FreeAlg Σ X .Carrier = FreeOn Σ X , {!   !}
FreeAlg Σ X .interp = ops

FreeAlgMorphism' : {Σ : Signature}{X : Type}{M : Alg Σ} → 
  (X → ⟨ M .Carrier ⟩ ) → 
  FreeOn Σ X → ⟨ M .Carrier ⟩  
FreeAlgMorphism' {Σ} {X} {M} f (inc x) = f x
FreeAlgMorphism' {Σ} {X} {M} f (ops o args) = 
  M .interp o (λ arg → FreeAlgMorphism' {Σ}{X}{M} f (args arg))

FreeAlgMorphism : {Σ : Signature}{X : Type}{M : Alg Σ} → 
  (X → ⟨ M  .Carrier ⟩ ) → 
  (ALG Σ)[ FreeAlg Σ X , M ] 
FreeAlgMorphism {Σ}{X}{M} gen .carmap = FreeAlgMorphism' {Σ}{X}{M} gen
FreeAlgMorphism gen .pres _ _ = refl


FreeAlgMorphism! : {Σ : Signature}{X : Type}{M : Alg Σ} → 
  {f g : (ALG Σ)[ FreeAlg Σ X , M ]} → 
  (∀ x → f .carmap (inc x) ≡ g .carmap (inc x)) → 
  f ≡ g
FreeAlgMorphism! {Σ}{X}{M}{f}{g} prf = AlgHom≡ (funExt goal) where 
  goal : (x : FreeOn Σ X) → f .carmap x ≡ g .carmap x 
  goal (inc x) = prf x
  goal (ops o x) = f .pres o x ∙ (λ i → interp M  o (λ a → goal (x a) i)) ∙ sym (g .pres o x)


FORGET : {T : Signature} → Functor (ALG T) (SET _) 
FORGET {T} .F-ob M = M .Carrier 
FORGET {T} .F-hom f = f .carmap
FORGET {T} .F-id = refl
FORGET {T} .F-seq _ _ = refl

record Algᴰ {Σ : Signature}(A : Alg Σ) : Type where 
  field 
    Carrierᴰ : (X : ⟨ A .Carrier ⟩ ) → hSet _
    interpᴰ : 
      (op : Op Σ)
      (args : Fin (arity Σ op) → ⟨ A. Carrier ⟩)
      (dargs : (x : Fin (arity Σ op)) → ⟨ Carrierᴰ (args x) ⟩) → 
      ⟨ Carrierᴰ (A .interp op args) ⟩
open Algᴰ 

record AlgHomᴰ {Sig : Signature} {M N : Alg Sig}(hom : AlgHom M N )(Mᴰ : Algᴰ  M)(Nᴰ : Algᴰ  N) : Type where 
  field 
    carmapᴰ : (m : ⟨ Carrier M ⟩) → ⟨ Mᴰ .Carrierᴰ m ⟩ →  ⟨ Nᴰ .Carrierᴰ (hom .carmap m) ⟩
    presᴰ : 
      (op : Sig .Op)
      (args : Fin (Sig .arity op) → ⟨ M .Carrier ⟩)
      (dargs : (x : Fin (Sig .arity op)) → ⟨ Mᴰ .Carrierᴰ (args x) ⟩ ) →
        PathP (λ i → ⟨ Nᴰ .Carrierᴰ (hom .pres op args  i) ⟩) 
          (carmapᴰ (M .interp op args) (Mᴰ .interpᴰ op args dargs)) 
          (Nᴰ .interpᴰ op  (λ x → hom .carmap (args x)) (λ x → carmapᴰ (args x) (dargs x))) 

open AlgHomᴰ

idHomᴰ : {Σ : Signature}{A : Alg Σ}{P : Algᴰ  A} → 
  AlgHomᴰ (ALG Σ .id) P P 
idHomᴰ {Σ} {A} {P} .carmapᴰ = λ m z → z
idHomᴰ {Σ} {A} {P} .presᴰ op args dargs = refl

_⋆AlgHomᴰ_ : 
  {Σ : Signature}{A B C : Alg Σ}
  {f : AlgHom A B}{g : AlgHom B C}
  {Aᴰ : Algᴰ  A}{Bᴰ : Algᴰ  B}{Cᴰ : Algᴰ  C} → 
  AlgHomᴰ f Aᴰ Bᴰ → AlgHomᴰ g Bᴰ Cᴰ → AlgHomᴰ ((ALG Σ ⋆ f) g) Aᴰ Cᴰ 
(_⋆AlgHomᴰ_ {f = f} fᴰ gᴰ) .carmapᴰ = λ a z → gᴰ .carmapᴰ (f .carmap a) (fᴰ .carmapᴰ a z)
(fᴰ ⋆AlgHomᴰ gᴰ) .presᴰ op args dargs = {!   !}
-- (f ⋆AlgHom g) .AlgHom.pres op args = cong (λ h → g .carmap h ) (f .pres op args) ∙ g .pres op λ x → f .carmap (args x)

ALGᴰ : {Σ : Signature} → Categoryᴰ (ALG Σ)  _ _ 
ob[ ALGᴰ {Σ} ] = Algᴰ {Σ}
ALGᴰ {Σ} .Hom[_][_,_] = AlgHomᴰ
ALGᴰ {Σ} .idᴰ = idHomᴰ
ALGᴰ {Σ} ._⋆ᴰ_ = _⋆AlgHomᴰ_
ALGᴰ {Σ} .⋆IdLᴰ = {!   !}
ALGᴰ {Σ} .⋆IdRᴰ = {!   !}
ALGᴰ {Σ} .⋆Assocᴰ = {!   !}
ALGᴰ {Σ} .isSetHomᴰ = {!   !}

AlgHomᴰ≡Prop : 
  {Σ : Signature} {M N : Alg Σ} 
  {hom : AlgHom M N}
  {Mᴰ : Algᴰ  M}{Nᴰ : Algᴰ  N}{f g : AlgHomᴰ hom Mᴰ Nᴰ} → 
  (triv : (n : ⟨ N .Carrier ⟩) → isProp ⟨ Nᴰ .Carrierᴰ n ⟩) → 
  f ≡ g
AlgHomᴰ≡Prop {Σ}{M}{N} {hom} {Mᴰ} {Nᴰ} {f} {g} triv i .carmapᴰ m x = 
  triv (hom .carmap m) (f .carmapᴰ m x) (g .carmapᴰ m x) i
AlgHomᴰ≡Prop {Σ}{M}{N} {hom} {Mᴰ} {Nᴰ} {f} {g} triv i .presᴰ op args dargs j = 
  triv (hom .pres op args j) (f .presᴰ op args dargs j) (g .presᴰ op args dargs j) {! i ∨ j  !}

