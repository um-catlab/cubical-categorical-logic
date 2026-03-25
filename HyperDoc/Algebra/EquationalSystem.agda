
{-# OPTIONS --type-in-type #-} 

module HyperDoc.Algebra.EquationalSystem where
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Adjoint
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Slice.Base
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Limits.Pullback

open Category
open Functor
open SliceOb 
open SliceHom
open NaturalBijection
open Iso
open Pullback

module basics where

  record Poly : Type where 
    constructor _◂_ 
    field 
      pos : Type 
      dir : pos → Type


  asFun : Poly → Functor (SET _) (SET _) 
  asFun (pos ◂ dir) .F-ob X = (Σ[ p ∈ pos ] (∀(d : dir p) → ⟨ X ⟩)) , {!   !}
  asFun (pos ◂ dir) .F-hom f (p , m) = p , λ d → f (m d)
  asFun (pos ◂ dir) .F-id = refl
  asFun (pos ◂ dir) .F-seq _ _ = refl

module categorical (C : Category _ _ )(pbs : Pullbacks C) where 

  

  Σf : {A B : C .ob} → C [ A , B ] → Functor (SliceCat C A) (SliceCat C B) 
  -- f : A → B ,  g : X → A  =>   X → B
  Σf {A} {B} f .F-ob (sliceob g) = sliceob (g ⋆⟨ C ⟩ f)
  {-
      f : A → B

      objects
        g : X → A 
        h : Y → A

      morphism
        s : X → Y 
        s.t. 

        s ; h ≡ g

      goal 
      morphism 
        X → Y
        s.t. triangle 

        X → Y 
        g|  |h
        A   A
        f| |f
          B


  -}
  Σf {A} {B} f .F-hom {sliceob {X} g} {sliceob {Y} h} (slicehom s tri) = slicehom s (sym (C .⋆Assoc _ _ _) ∙ cong (λ h → seq' C h f) tri)
  Σf {A} {B} f .F-id = SliceHom-≡-intro' C B refl
  Σf {A} {B} f .F-seq _ _ = SliceHom-≡-intro' C B refl

  Rf : {A B : C .ob} → C [ A , B ] → Functor (SliceCat C B) (SliceCat C A) 
  {-
    have 
      f : A → B 
      g : X → B   

      need a map into A 
      use the top map in the pullback diagram 

      X×pbA ---> A 
       |         |
       |    g    | f
       X ------> B
  -}
  Rf {A} {B} f .F-ob (sliceob {X} g) = sliceob (pbPr₁ (pbs (cospan _ _ _ f g)))
  {-
    we have f : A → B 
    and triangle 
          m
      X ----> Y 
      g \   / h
          B

    need a map between the vertices of two pullback squares C [ X×pbA , Y×pbA ]
    sq1: 
             t
      X×pbA ---> A 
       |         |
       |    g    | f
       X ------> B

    sq2:
            t'
      Y×pbA ---> A 
       |         |
       |    h    | f
       Y ------> B

    commute 
      s.t. 


    

  -}
  Rf {A} {B} f .F-hom {sliceob {X} g} {sliceob {Y} h} (slicehom m m-comm) = slicehom mor tri where 

    sq1 : Pullback C (cospan _ _ _ f g) 
    sq1 = pbs (cospan _ _ _ f g)

    t : C [ sq1 .pbOb , A ] 
    t = sq1 .pbPr₁

    sq2 : Pullback C (cospan _ _ _ f h) 
    sq2 = pbs (cospan _ _ _ f h)

    t' : C [ sq2 .pbOb , A ] 
    t' = sq2 .pbPr₁

    mor : C [ sq1 .pbOb , sq2 .pbOb ] 
    mor = pullbackArrow sq2 t ((C ⋆ sq1 .pbPr₂) m)  (sq1 .pbCommutes ∙ cong (λ h → (C ⋆ sq1 .pbPr₂) h) (sym m-comm) ∙ sym (C .⋆Assoc _ _ _))

    tri : mor ⋆⟨ C ⟩ t' ≡ t 
    tri = sym (pullbackArrowPr₁ C (pbs (cospan A B Y f h)) t (((C ⋆ sq1 .pbPr₂) m)) ((sq1 .pbCommutes ∙ cong (λ h → (C ⋆ sq1 .pbPr₂) h) (sym m-comm) ∙ sym (C .⋆Assoc _ _ _))))

  Rf {A} {B} f .F-id = SliceHom-≡-intro' C A {!   !}
  -- (pullbackArrowUnique {!  pbs ?  !}  (sym (C .⋆IdL _)) (sym (C .⋆IdL _)))
  Rf {A} {B} f .F-seq _ _ = SliceHom-≡-intro' C A {!   !}

  Σ⊣R : {A B : C .ob} → (f : C [ A , B ]) → isRightAdjoint (Rf f) 
  Σ⊣R f .fst = Σf f
  Σ⊣R f .snd ._⊣_.adjIso .fun = {!   !}
  Σ⊣R f .snd ._⊣_.adjIso .inv = {!   !}
  Σ⊣R f .snd ._⊣_.adjIso .sec = {!   !}
  Σ⊣R f .snd ._⊣_.adjIso .ret = {!   !}
  Σ⊣R f .snd ._⊣_.adjNatInD = {!   !}
  Σ⊣R f .snd ._⊣_.adjNatInC = {!   !}

module Indexed where 
  open import Cubical.Data.W.Indexed
  Foo : Type 
  Foo = IW {!   !} {!   !} {!   !} {!   !}
  {-
  record Poly (I J : Type) : Type₁ where
    field
      Shape : Type
      Pos   : Shape → Type
      src   : ∀ s → Pos s → I
      tgt   : Shape → J

  data Ty : Type where
    Bool : Ty
    _⇒_  : Ty → Ty → Ty

  data Ctx : Type where
    ε   : Ctx
    _,_ : Ctx → Ty → Ctx

  data Shape : Type where
    var   : (Γ : Ctx) → (A : Ty) → Shape
    true  : (Γ : Ctx) → Shape
    false : (Γ : Ctx) → Shape
    app   : (Γ : Ctx) → (A B : Ty) → Shape
    lam   : (Γ : Ctx) → (A B : Ty) → Shape

  open import Cubical.Data.Sigma

  tgt : Shape → Ctx × Ty
  tgt (var Γ A)   = (Γ , A)
  tgt (true Γ)    = (Γ , Bool)
  tgt (false Γ)   = (Γ , Bool)
  tgt (app Γ A B) = (Γ , B)
  tgt (lam Γ A B) = (Γ , A ⇒ B)

  data Pos : Shape → Type where
  -- var: no recursive arguments
  -- true/false: none

    app-fun : ∀ {Γ A B} → Pos (app Γ A B)
    app-arg : ∀ {Γ A B} → Pos (app Γ A B)

    lam-body : ∀ {Γ A B} → Pos (lam Γ A B)

  src : ∀ s → Pos s → (Ctx × Ty)
  src (app Γ A B) app-fun = (Γ , A ⇒ B)
  src (app Γ A B) app-arg = (Γ , A)
  src (lam Γ A B) lam-body = (Γ , A) , B

  STLCPoly : Poly (Ctx × Ty) (Ctx × Ty)
  STLCPoly .Poly.Shape = Shape
  STLCPoly .Poly.Pos   = Pos
  STLCPoly .Poly.src   = src
  STLCPoly .Poly.tgt   = tgt

  ⟦_⟧ : Poly (Ctx × Ty) (Ctx × Ty)
     → ((Ctx × Ty) → Type)
     → ((Ctx × Ty) → Type)

  ⟦ P ⟧ X (Γ , A) =
    Σ[ s ∈ Shape ]
      (tgt s ≡ (Γ , A)) ×
      ((p : Pos s) → X (src s p))

-}