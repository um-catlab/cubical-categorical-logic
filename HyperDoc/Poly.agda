{-# OPTIONS --type-in-type #-}

-- for Generalized polynomials
module HyperDoc.Poly where 

open import Cubical.Data.Nat
open import Cubical.Data.Unit 
open import Cubical.Data.Sum renaming (map to ⊎map ; rec to ⊎rec)
open import Cubical.Data.FinData 
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

-- open import Cubical.Categories.Presheaf.Properties 
open import Cubical.Categories.Presheaf.Morphism.Alt
open import HyperDoc.Lib 
open import Cubical.Categories.NaturalTransformation
open NatTrans
open PshHom

open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets

-- open import HyperDoc.FinDataUP
open Category
open Functor
open FinSumChar renaming (inv to match)

record FinPoly (ℓ : Level) : Type (ℓ-suc ℓ) where 
  constructor _◂_ 
  field 
    pos : ℕ 
    dir : Fin pos → hSet ℓ

⦅_⦆ : {ℓ  : Level} → FinPoly ℓ  → hSet ℓ → hSet ℓ 
⦅ pos ◂ dir ⦆ X .fst = Σ[ x ∈ Fin pos ] (⟨ dir x ⟩ → ⟨ X ⟩)
⦅ pos ◂ dir ⦆ X .snd = {!   !}
  -- (Σ[ p ∈ ⟨ pos ⟩  ] ((⟨ dir p ⟩ → ⟨ X ⟩ ))) , isSetΣ (pos .snd) λ _ → isSet→ (X .snd)

-- Y ↦ Σ(i ∈ I) SET[ Xᵢ , Y ]
den : {ℓ  : Level} → FinPoly ℓ → Functor (SET ℓ) (SET ℓ) 
den P .F-ob X = ⦅ P ⦆ X
den P .F-hom f (n , d) = n , λ z → f (d z)
den P .F-id = refl
den P .F-seq _ _ = refl

-- yoneda embedding in SET^op
Yo : {ℓ : Level} → hSet ℓ  → Functor (SET ℓ) (SET ℓ)
Yo {ℓ} X = (SET ℓ)[ X ,-]

-- P is presheaf in SET^op
Repr : {ℓ : Level} → (P : Functor (SET ℓ) (SET ℓ)) → Type (ℓ-suc ℓ)
Repr {ℓ} P = Σ[ X ∈ hSet ℓ ] PshIso  (Yo X ∘F from^op^op) (P ∘F from^op^op) 

-- Lets look at a simple polynomial
-- a constant monomial
-- P(X) := A
const : {ℓ : Level} → hSet ℓ → FinPoly ℓ 
const X = 1 ◂ λ _ → X


-- This is representable (by definition) in SET^op
constRepr : {ℓ : Level} → (X : hSet ℓ) → Repr (den (const X))
constRepr X .fst = X
constRepr X .snd .PshIso.trans .N-ob Y f = zero , f
constRepr X .snd .PshIso.trans .N-hom Y Y' f g = refl
constRepr X .snd .PshIso.nIso Y .fst (zero , f) x  = f x
constRepr X .snd .PshIso.nIso Y .snd .fst (zero , f) = refl
constRepr X .snd .PshIso.nIso Y .snd .snd f = refl
-- variable monomial 
-- P(X) := X 
-- which is also representable in Set
Var : FinPoly ℓ-zero
Var = const ((Fin 1) , isSetFin)

VarRepr : Repr (den Var) 
VarRepr .fst = {!   !}
VarRepr .snd = {!   !}



_⊕_ : FinPoly ℓ-zero → FinPoly ℓ-zero → FinPoly ℓ-zero
(n ◂ dir) ⊕ (m ◂ dir') = (n + m) ◂ λ x → ⊎rec dir dir' (match n m x)

{-
  A Presheaf F : C^op → Set is representable if it is naturally isomorphic to the 
  yoneda embedding
  
  Yo(A) : C^op → Set 
  Yo(A) := C[-, A ]

  ∀ A, F ≅ Yo(A)
-}

CProd : (A A' : hSet ℓ-zero) → FinPoly ℓ-zero 
CProd A A' = const A ⊕ const A'

CProdFun : (A A' : hSet ℓ-zero) → Functor (SET _) (SET _) 
CProdFun A A' = den (CProd A A')

obs : (A A' X : hSet ℓ-zero) → CProdFun A A' .F-ob X ≡ {!   !}
obs A A' X = refl


--Prod : FinPoly ℓ-zero
--Prod = Var ⊕ Var



-- SET[ X₁ + X₂ + ... , Y ] ≅ SET [X₁ , Y] + SET [ X₂ + Y ] + ...
hmm : {ℓ : Level}{X : hSet ℓ}((n ◂ dir ) : FinPoly ℓ) → 
  Σ (Fin n) (λ x → fst (dir x) → fst X) → 
  Σ (Fin n) (λ x → fst (dir x)) → X .fst
hmm (suc n ◂ dir) f (m , d) = f .snd {!   !}

polyRep : {ℓ  : Level} → (P : FinPoly ℓ) →  Representation ((SET ℓ)^op) (den P ∘F from^op^op) 
polyRep (n ◂ dir) .fst = (Σ[ x ∈ Fin n ] ⟨ dir x ⟩) , {!   !}
polyRep (n ◂ dir) .snd .PshIso.trans .N-ob X f = {!n   !}
polyRep (n ◂ dir) .snd .PshIso.trans .N-hom = {!   !}
polyRep (n ◂ dir) .snd .PshIso.nIso X .fst = hmm {X = X} (n ◂ dir)
polyRep (n ◂ dir) .snd .PshIso.nIso X .snd = {!   !}

CProdPsh : (A A' : hSet ℓ-zero) → Representation ((SET ℓ-zero) ^op) (den (CProd A A') ∘F from^op^op)
CProdPsh A A' .fst = (⟨ A ⟩  ⊎ ⟨ A' ⟩) , {!   !}
CProdPsh A A' .snd .PshIso.trans .N-ob B f = {!   !} , {!   !}
CProdPsh A A' .snd .PshIso.trans .N-hom = {!   !}
CProdPsh A A' .snd .PshIso.nIso B .fst = {!   !}
CProdPsh A A' .snd .PshIso.nIso B .snd = {!   !}


module Generalized where 
  open import Cubical.Categories.Presheaf
  open import Cubical.Categories.Presheaf.KanExtension

  record GPoly : Type _ where 
    field 
      A I' J' B : Category _ _ 
      s : Functor I' A 
      f : Functor I' J' 
      t : Functor J' B

    s^* : Functor (PresheafCategory A _) (PresheafCategory I' _) 
    s^* = precomposeF (SET _) (s ^opF)

    open Ran _ f
    f_* : Functor (PresheafCategory I' _)  (PresheafCategory J' _) 
    f_* = Ran

    open Lan _ t 
    t_!  : Functor ((PresheafCategory J' _)) ((PresheafCategory B _)) 
    t_! = Lan

    denGP : Functor (PresheafCategory A _) (PresheafCategory B _) 
    denGP = (t_! ∘F f_*) ∘F s^*

  open GPoly

  ex : GPoly 
  ex .A = {!   !}
  ex .I' = {!   !}
  ex .J' = {!   !}
  ex .B = {!   !}
  ex .s = {!   !}
  ex .f = {!   !}
  ex .t = {!   !}

module DiscreteGeneralized where 
  open import Cubical.Categories.Presheaf.KanExtension

  _n∙_ : {ℓ ℓ' : Level } → ℕ → Category ℓ ℓ' → Type ℓ 
  _n∙_ n C = Σ[ x ∈ Fin n ] C .ob

  ∇n : {ℓ ℓ' : Level }{C : Category ℓ ℓ'}{n : ℕ} → (d : n n∙ C) → C [ d .snd , d .snd ]
  ∇n {C = C} d = C .id

  LC : Category _ _ 
  LC = ?

{-}
ProdF : Functor (SET ℓ-zero) (SET ℓ-zero )
ProdF = den Prod

hmm : (X : hSet ℓ-zero) → {!   !} 
hmm X = ProdF .F-ob X

what = {! hmm _ .fst   !}

ProdPsh : Representation ((SET ℓ-zero) ^op) (ProdF ∘F from^op^op) 
ProdPsh .fst = {!   !}
ProdPsh .snd = {!   !}
-}
{-}
record Poly (ℓ : Level): Type (ℓ-suc ℓ) where 
  constructor _◂_ 
  field 
    pos : hSet ℓ 
    dir : ⟨ pos ⟩  → hSet ℓ
open Poly

Var : {ℓ : Level} → Poly ℓ 
Var = (Fin 1 , isSetFin) ◂ λ _ → (Fin 1) , isSetFin

𝟙 : {ℓ : Level} → Poly ℓ 
𝟙 = ((Fin 1) , isSetFin) ◂ λ _ → Fin 0 , isSetFin

_⊕_ : {ℓ : Level} → Poly ℓ → Poly ℓ → Poly ℓ 
(pos₁ ◂ dir₁) ⊕ (pos₂ ◂ dir₂) = 
  ((⟨ pos₁ ⟩ ⊎ ⟨ pos₂ ⟩) , isSet⊎ (pos₁ .snd) (pos₂ .snd)) ◂ λ {(inl x) → ⟨ dir₁ x ⟩ , dir₁ x .snd
                                                              ; (inr x) → ⟨ dir₂ x ⟩ , dir₂ x .snd}

⦅_⦆ : {ℓ  : Level} → Poly ℓ  → hSet ℓ → hSet ℓ 
⦅ pos ◂ dir ⦆ X = (Σ[ p ∈ ⟨ pos ⟩  ] ((⟨ dir p ⟩ → ⟨ X ⟩ ))) , isSetΣ (pos .snd) λ _ → isSet→ (X .snd)

den : {ℓ  : Level} → Poly ℓ → Functor (SET ℓ) (SET ℓ) 
den P .F-ob X = ⦅ P ⦆ X 
den (pos ◂ dir) .F-hom f (p , d) = p , λ d' → f (d d')
den (pos ◂ dir) .F-id = funExt λ _ → refl
den (pos ◂ dir) .F-seq _ _ = funExt λ _ → refl

data μ {ℓ  : Level} (P : Poly ℓ ) : Type ℓ where 
  unfold : ⟨ ⦅ P ⦆ ((μ P) , {!   !}) ⟩  → μ P 


open import Cubical.Categories.Presheaf.Representable hiding (Representation)
open import Cubical.Categories.Presheaf.Properties 
open import Cubical.Categories.Presheaf.Morphism.Alt
open import HyperDoc.Lib 
open import Cubical.Categories.NaturalTransformation
open NatTrans
open PshHom
polyRep : {ℓ : Level} → (P : Poly ℓ) → Representation ((SET ℓ) ^op) (den P ∘F from^op^op)
polyRep {ℓ} (pos ◂ dir) .fst = pos
polyRep {ℓ} (pos ◂ dir) .snd .PshIso.trans .N-ob X dir' = {!  !} , {!   !}
polyRep {ℓ} (pos ◂ dir) .snd .PshIso.trans .N-hom = {!   !}
polyRep {ℓ} (pos ◂ dir) .snd .PshIso.nIso = {!   !}

    
module ExpEx where 



  NatP : Poly ℓ-zero 
  NatP .pos .fst = Fin 2
  NatP .pos .snd = isSetFin
  NatP .dir zero .fst = Fin 0
  NatP .dir zero .snd = isSetFin
  NatP .dir one .fst = Fin 1
  NatP .dir one .snd = isSetFin

  NatP' : Poly ℓ-zero 
  NatP' = 𝟙 ⊕ Var

  Nat' : Type ℓ-zero 
  Nat' = μ NatP'

  z' : Nat' 
  z' = unfold ((inl zero) , λ ())

  s' : Nat' → Nat' 
  s' n = unfold ((inr zero) , λ _ → n)

  Nat : Type ℓ-zero 
  Nat = μ NatP

  z : Nat 
  z = unfold (zero , (λ ()))

  s : Nat → Nat 
  s n = unfold (one , (λ _ → n))

  NatF : Functor (SET ℓ-zero) (SET ℓ-zero) 
  NatF = den NatP

  -}