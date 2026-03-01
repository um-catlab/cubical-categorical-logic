{-# OPTIONS --type-in-type #-}
-- this is for hacking, i dont care
-- do not read for your own sanity.. 
-- im using this as a blackboard to check my paper math

module HyperDoc.Example where 

  open import Cubical.Foundations.Prelude hiding (_∧_)
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Structure
  
  open import Cubical.Data.Nat
  open import Cubical.Data.Empty
  open import Cubical.Data.Sigma
  open import Cubical.Data.FinData
  open import Cubical.Data.List using (List ; [] ; _++_)
  open import Cubical.Data.List.Properties
  open import Cubical.Data.Unit
  open import Cubical.Categories.Category hiding (isUnivalent)
  open import Cubical.Categories.Functor
  open import Cubical.Categories.Constructions.BinProduct
  open import Cubical.Categories.NaturalTransformation
  open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
  open import Cubical.Categories.Instances.Preorders.Monotone
  open import Cubical.Categories.Instances.Posets.Base
  open import Cubical.Categories.Presheaf.Constructions.Unit
  open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)
  open import HyperDoc.Lib
  open import Cubical.Relation.Binary.Preorder
  open import Cubical.Categories.Displayed.Base
  open import Cubical.Categories.Instances.Sets
  open import Cubical.Categories.Displayed.Functor
  open import Cubical.Categories.Displayed.BinProduct 
  open import Cubical.Categories.Displayed.Instances.Sets
  open import HyperDoc.Syntax
  open import Cubical.Categories.Displayed.Section.Base
  open import HyperDoc.Connectives.Connectives 
  open import Cubical.Categories.Limits.Terminal.More
  open import Cubical.Categories.Presheaf.Representable hiding (Representation)
  open import Agda.Builtin.Cubical.Equiv
  open import Cubical.Categories.Displayed.Limits.Terminal
  open import Cubical.Categories.Displayed.Presheaf.Representable
  open import Cubical.Categories.Displayed.Constructions.Reindex.Base renaming (reindex to reindexᴰ)
  open import Cubical.Categories.Displayed.Bifunctor
  open import Cubical.Categories.Bifunctor
  open import Cubical.Data.Sum
  open import Cubical.HITs.PropositionalTruncation.Base
  open import Cubical.HITs.PropositionalTruncation.Properties renaming (rec to hrec ; map to hmap)
  open PreorderStr
  open Category
  open Functor
  open NatTrans  
  open PshIso
  open PshHom
  open Categoryᴰ
  open Functorᴰ
  open Bifunctorᴰ
  open UniversalElement
  



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

  record DAlg {Σ : Signature}(A : Alg Σ) : Type where 
    field 
      Carrierᴰ : (X : ⟨ A .Carrier ⟩ ) → hSet _
      interpᴰ : 
        (op : Op Σ)
        (args : Fin (arity Σ op) → ⟨ A. Carrier ⟩)
        (dargs : (x : Fin (arity Σ op)) → ⟨ Carrierᴰ (args x) ⟩) → 
        ⟨ Carrierᴰ (A .interp op args) ⟩
  open DAlg

  record AlgHomᴰ {Sig : Signature} {M N : Alg Sig}(hom : AlgHom M N )(Mᴰ : DAlg M)(Nᴰ : DAlg N) : Type where 
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

  idHomᴰ : {Σ : Signature}{A : Alg Σ}{P : DAlg A} → 
    AlgHomᴰ (ALG Σ .id) P P 
  idHomᴰ {Σ} {A} {P} .carmapᴰ = λ m z → z
  idHomᴰ {Σ} {A} {P} .presᴰ op args dargs = refl

  _⋆AlgHomᴰ_ : 
    {Σ : Signature}{A B C : Alg Σ}
    {f : AlgHom A B}{g : AlgHom B C}
    {Aᴰ : DAlg A}{Bᴰ : DAlg B}{Cᴰ : DAlg C} → 
    AlgHomᴰ f Aᴰ Bᴰ → AlgHomᴰ g Bᴰ Cᴰ → AlgHomᴰ ((ALG Σ ⋆ f) g) Aᴰ Cᴰ 
  (_⋆AlgHomᴰ_ {f = f} fᴰ gᴰ) .carmapᴰ = λ a z → gᴰ .carmapᴰ (f .carmap a) (fᴰ .carmapᴰ a z)
  (fᴰ ⋆AlgHomᴰ gᴰ) .presᴰ op args dargs = {!   !}
  -- (f ⋆AlgHom g) .AlgHom.pres op args = cong (λ h → g .carmap h ) (f .pres op args) ∙ g .pres op λ x → f .carmap (args x)

  ALGᴰ : {Σ : Signature} → Categoryᴰ (ALG Σ)  _ _ 
  ob[ ALGᴰ {Σ} ] = DAlg{Σ}
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
    {Mᴰ : DAlg M}{Nᴰ : DAlg N}{f g : AlgHomᴰ hom Mᴰ Nᴰ} → 
    (triv : (n : ⟨ N .Carrier ⟩) → isProp ⟨ Nᴰ .Carrierᴰ n ⟩) → 
    f ≡ g
  AlgHomᴰ≡Prop {Σ}{M}{N} {hom} {Mᴰ} {Nᴰ} {f} {g} triv i .carmapᴰ m x = 
    triv (hom .carmap m) (f .carmapᴰ m x) (g .carmapᴰ m x) i
  AlgHomᴰ≡Prop {Σ}{M}{N} {hom} {Mᴰ} {Nᴰ} {f} {g} triv i .presᴰ op args dargs j = 
    triv (hom .pres op args j) (f .presᴰ op args dargs j) (g .presᴰ op args dargs j) {! i ∨ j  !}


  open Theory
  open Equation
  open Model


  record CBPVModel (Σ : Signature) : Type where 
    field 
      V : Category _ _ 
      C : Category _ _ 
      O : Functor ((V ^op) ×C C) (ALG Σ) 

    O[_,-] : (v : ob V) → Functor C (ALG Σ) 
    O[_,-] v = O ∘F rinj _ _ v

    O[-,_] : (c : ob C) → Functor (V ^op) (ALG Σ) 
    O[-,_] c = O ∘F linj _ _ c

    O[_,_] : ob V → ob C → ob (ALG Σ) 
    O[_,_] v c = O .F-ob (v , c)

    O'[_,_] : ob V → ob C → Type 
    O'[_,_] v c = ⟨ O .F-ob (v , c) .Carrier ⟩ 

    lcomp : ∀{v v' c} → V [ v , v' ] → (ALG Σ) [ O[ v' , c ] , O[ v , c ] ]
    lcomp f = O .F-hom (f , (C .id))

    rcomp : ∀{v c c'} → C [ c , c' ] → (ALG Σ) [ O[ v , c ] , O[ v , c' ] ]
    rcomp g = O .F-hom ((V .id) , g)

    lrcomp : ∀{v v' c c'} → V [ v' , v ] → C [ c , c' ] → (ALG Σ) [ O[ v , c ] , O[ v' , c' ] ]
    lrcomp V S = O .F-hom (V , S)

    lcompId : ∀{v c}{M : O'[ v , c ]} → lcomp (V .id) .carmap M ≡ M
    lcompId {v}{c}{M} i = O .F-id  i .carmap M 
      
    rcompId : ∀{v c}{M : O'[ v , c ]} → rcomp (C .id) .carmap M ≡ M
    rcompId {v}{c}{M} i = O .F-id  i .carmap M 

    rcompSeq : ∀ {v c c' c''}{S : C [ c , c' ]}{S' : C [ c' , c'' ]}{M : O'[ v , c ]} → 
      rcomp  S' .carmap (rcomp S .carmap M) ≡ rcomp (S ⋆⟨ C ⟩ S') .carmap M
    rcompSeq {S = S}{S'}{M} = {!   !} ∙ {! O .F-seq (V .id , (C ⋆ S) S')  !}
    --cong (λ h → h .carmap M ) {! cong₂ (O .F-hom) (cong₂ _,_ (V .⋆IdL _) refl)  !}
    {-
    

  rcompSeq : ∀ {v c c' c''}{S : C [ c , c' ]}{S' : C [ c' , c'' ]}{M : O[ v , c ]} → 
    rcomp  S' (rcomp S M) ≡ rcomp (S ⋆⟨ C ⟩ S') M
  rcompSeq {S = S}{S'}{M} =  funExt⁻ (sym (O .F-seq (V .id , S) (V .id , S'))) M ∙ cong₂ (O .F-hom) (cong₂ _,_ (V .⋆IdL _) refl) refl

  lcompSeq : ∀ {v v' v'' c }{W : V [ v , v' ]}{Y : V [ v' , v'' ]}{M : O[ v'' , c ]} → 
    lcomp  W (lcomp Y M) ≡ lcomp (W ⋆⟨ V ⟩ Y) M
  lcompSeq {W = W}{Y}{M}= funExt⁻ (sym (O .F-seq (Y , C .id) (W , C .id))) M ∙ cong₂ (O .F-hom) (cong₂ _,_ refl (C .⋆IdL _)) refl

  lrSeq : ∀ {A A' B B'}{W : V [ A , A' ]}{M : O[ A' , B ]}{S : C [ B , B' ]} → 
    lcomp W (rcomp S M) ≡ rcomp S (lcomp W M)
  lrSeq {W = W}{M}{S} = 
    funExt⁻ (sym (O .F-seq _ _)) M  
    ∙ cong₂ (O .F-hom ) (cong₂ _,_ (V .⋆IdR _ ∙ sym (V .⋆IdL _)) (C .⋆IdR _ ∙ sym (C .⋆IdL _))) refl 
    ∙ funExt⁻ (O .F-seq _ _ ) M
    -}


  record CBPVMorphism {Σ : Signature} (M N : CBPVModel Σ) : Type where
    private 
      module M = CBPVModel M 
      module N = CBPVModel N
    field 
      FV : Functor M.V N.V 
      FC : Functor M.C N.C 
      FO : NatTrans M.O (N.O ∘F ((FV ^opF) ×F FC)) 
  
  idCBPVMorphism : {Σ : Signature} {M : CBPVModel Σ} → CBPVMorphism M M 
  idCBPVMorphism .CBPVMorphism.FV = Id
  idCBPVMorphism .CBPVMorphism.FC = Id
  idCBPVMorphism .CBPVMorphism.FO .N-ob x = idHom
  idCBPVMorphism .CBPVMorphism.FO .N-hom f = AlgHom≡ refl

  record CBPVModelᴰ {Σ : Signature}(M : CBPVModel Σ) : Type where 
    open CBPVModel M
    field 
      Vᴰ : Categoryᴰ V _ _ 
      Cᴰ : Categoryᴰ C _ _ 
      Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) (ALGᴰ {Σ})

  module TypeStructure {Σ : Signature} (M : CBPVModel Σ)  where 
    open CBPVModel M

    HasV𝟙 : Type 
    HasV𝟙 = Representation V UnitPsh

    HasUTy : Type 
    HasUTy = (B : ob C) → Representation V (FORGET ∘F O[-, B ])

  module Syntax (Σ : Signature) where 

    mutual 
      data VTy : Type where 
        𝟙 : VTy
        U : CTy → VTy

      data CTy : Type where 
        Ans : CTy

    data _⊢v_ : (A A' : VTy) → Type 
    data _⊢c_ : (A : VTy)(B : CTy) → Type 
    data _⊢k_ : (B B' : CTy) → Type 

    subC' : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B
    force' :  ∀{B} → U B ⊢c B

    data _⊢v_  where
      -- category 
      subV : ∀ {A A' A''} → A ⊢v A' → A' ⊢v A'' → A ⊢v A''
      var : ∀ {A} → A ⊢v A
      subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
      subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
      subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
        subV (subV V W) Y ≡ subV V (subV W Y)
      isSet⊢v : ∀{A A'} → isSet (A ⊢v A')

      -- type structure
      thunk : {A : VTy}{B : CTy} → (M : A ⊢c B) → A ⊢v U B
      Uη : ∀{A B}{V : A ⊢v U B} →  thunk (subC' V force') ≡ V
      tt : ∀{A} → A ⊢v 𝟙
      η𝟙 : ∀{A} → (V : A ⊢v 𝟙) → tt ≡ V

    data _⊢k_ where
      -- category 
      kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
      hole : ∀ {B} → B ⊢k B
      kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
      kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
      kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
        kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)
      isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

    data _⊢c_ where 
      -- profunctor      
      subC : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B
      plug : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B'
      plugId : ∀ {A B}{M : A ⊢c B} → plug (hole {B}) M ≡ M
      subCId : ∀ {A B}{M : A ⊢c B} → subC (var {A}) M ≡ M
      plugDist : ∀ {A B B' B''}{S : B ⊢k B'}{S' : B' ⊢k B''}{M : A ⊢c B} → --rcomp
        plug S' (plug S M) ≡ plug (kcomp S S') M
      subDist : ∀ {A A' A'' B}{V : A ⊢v A'}{V' : A' ⊢v A''}{M : A'' ⊢c B} → --lcomp
        subC V (subC V' M) ≡ subC (subV V V') M
      plugSub : ∀ {A A' B B'}{V : A ⊢v A'}{M : A' ⊢c B}{S : B ⊢k B'} → 
        subC V (plug S M) ≡ plug S (subC V M)
      isSet⊢c : ∀{A B} → isSet (A ⊢c B)

      -- algebra structure
      ops : ∀(A : VTy)(B : CTy)(op : Σ .Op) →  
        (Fin (Σ .arity op) → A ⊢c B) → A ⊢c B
      opsSub : ∀{A A' : VTy}{B : CTy}(V : A ⊢v A')(op : Σ .Op) →  
        (args : Fin (Σ .arity op) → A' ⊢c B) → 
        subC V (ops A' B op args) ≡ ops A B op (λ x → subC V (args x))
      opsPlug :  ∀{A : VTy}{B B' : CTy}(S : B ⊢k B')(op : Σ .Op) →  
        (args : Fin (Σ .arity op) → A ⊢c B) → 
        plug S (ops  A B op args) ≡ ops A B' op (λ x → plug S (args x))

      -- type structure
      force : {B : CTy} → U B ⊢c B      
      yes : 𝟙 ⊢c Ans 
      no : 𝟙 ⊢c Ans 
      Uβ : ∀ {A B} → {M : A ⊢c B} → subC (thunk M) force ≡ M

    subC' = subC
    force' = force

  module SyntacticModel (Σ : Signature)  where 
    open Syntax Σ

    V : Category ℓ-zero ℓ-zero
    V .ob = VTy
    V .Hom[_,_] = _⊢v_
    V .id = var
    V ._⋆_ = subV
    V .⋆IdL = subVIdl
    V .⋆IdR = subVIdr
    V .⋆Assoc = subVAssoc
    V .isSetHom = isSet⊢v

    C : Category ℓ-zero ℓ-zero 
    C .ob = CTy
    C .Hom[_,_] = _⊢k_
    C .id = hole
    C ._⋆_ = kcomp
    C .⋆IdL = kcompIdl
    C .⋆IdR = kcompIdr
    C .⋆Assoc = kcompAssoc
    C .isSetHom = isSet⊢k

    FreeCompAlg : VTy → CTy → Alg Σ
    FreeCompAlg A B .Carrier = A ⊢c B , isSet⊢c
    FreeCompAlg A B .interp = ops A B
    
    O : Functor (V ^op ×C C) (ALG Σ) 
    O .F-ob (A , B) = FreeCompAlg A B
    O .F-hom (V , S) .carmap M = plug S (subC V M)
    O .F-hom (V , S) .pres op args = cong (λ h →  plug S h) (opsSub V op args) ∙ opsPlug S op λ x → subC V (args x)
    O .F-id = AlgHom≡ (funExt λ M → plugId ∙ subCId)
    O .F-seq (V , S)(V' , S') = AlgHom≡ (funExt λ M → sym plugDist ∙ cong₂ plug refl (sym plugSub ∙ sym subDist ∙ cong₂ subC refl plugSub))

    SynModel : CBPVModel Σ 
    SynModel .CBPVModel.V = V
    SynModel .CBPVModel.C = C
    SynModel .CBPVModel.O = O 

    open TypeStructure SynModel

    has𝟙 : HasV𝟙 
    has𝟙 .fst = 𝟙
    has𝟙 .snd .trans .N-ob = λ c _ → tt
    has𝟙 .snd .trans .N-hom _ _ _ _ = refl
    has𝟙 .snd .nIso A .fst tt = tt
    has𝟙 .snd .nIso A .snd .fst tt = refl
    has𝟙 .snd .nIso A .snd .snd = η𝟙

    hasUTy : HasUTy
    hasUTy B .fst = U B
    hasUTy B .snd .trans .N-ob A V = subC V force
    hasUTy B .snd .trans .N-hom A A' V W = sym subDist ∙ sym plugId
    hasUTy B .snd .nIso A .fst = thunk
    hasUTy B .snd .nIso A .snd .fst M = Uβ
    hasUTy B .snd .nIso A .snd .snd V = Uη


  Hom^op :  Functor ((POSET _ _) ×C (POSET _ _)^op) (SET _)
  Hom^op .F-ob (P , Q) = (POSET _ _) [ Q , P ] , (POSET _ _) .isSetHom
  Hom^op .F-hom {(A , B)}{(A' , B')} (f , g) h = MonComp g (MonComp h f)
  Hom^op .F-id = funExt λ _ → eqMon _ _ refl
  Hom^op .F-seq _ _ = funExt λ _ → eqMon _ _ refl

  record Logic {Σ : Signature} (M : CBPVModel Σ) : Type _ where 
    open CBPVModel M
    field 
      VH : Functor (V ^op) (POSET _ _)
      CH : Functor (C ^op) (POSET _ _)
      Sq : NatTrans (FORGET ∘F O) (Hom^op ∘F (VH ×F ((CH ^opF) ∘F to^op^op)))

    private 
      module VL = HDSyntax VH
      module CL = HDSyntax CH
        
    pull : {A : V .ob}{B : C .ob}(M : O'[ A , B ])  
      → MonFun (F-ob CH B .fst) (F-ob VH A .fst)
    pull {A} {B} M = Sq .N-ob (A , B) M
    
    field 
      pullOp : 
        {A : V .ob}{B : C .ob}
        (op : Op Σ)
        (args : (Fin (arity Σ op) → O'[ A , B ]))
        (P : VL.F∣ A ∣)(Q : CL.F∣ B ∣)
        (dargs : (x : Fin (arity Σ op)) → A VL.◂ P ≤ (pull (args x) $ Q))→ 
        A VL.◂ P ≤ (pull (O[ A , B ] .interp op args) $ Q)


    pullComp : ∀ {A A' B B'}(V : V [ A' , A ])(S : C [ B , B' ])(M : O'[ A , B ]) → 
      pull (lrcomp V S .carmap M) ≡ MonComp (CH .F-hom S) (MonComp (pull M) (VH .F-hom V))
    pullComp V S M = funExt⁻ (Sq .N-hom (V , S)) M

    pullLComp : ∀ {A A' B}(V : V [ A' , A ])(M : O'[ A , B ]) → 
      pull (lcomp V .carmap M) ≡ MonComp (pull M) (VH .F-hom V)
    pullLComp V M = pullComp V (C .id) M  ∙ cong (λ h → MonComp h (MonComp (pull M) (VH .F-hom V))) (CH .F-id)

    pullRComp :  ∀ {A B B'}(S : C [ B , B' ])(M : O'[ A , B ]) → 
      pull (rcomp S .carmap M) ≡ MonComp (CH .F-hom S) (pull M)
    pullRComp S M = pullComp (V .id) S M ∙ cong₂ MonComp refl (VH .F-id)


  record InterpGen {Σ : Signature} 
      (L : Logic (SyntacticModel.SynModel Σ))
      (⊤ : L⊤.Has⊤ (Logic.VH L)): Type where 
    open Logic L
    open Syntax Σ 
    open L⊤.HA 
    private
      module LV = HDSyntax VH 
      module LC = HDSyntax CH 
    field 
      interpAns : LC.F∣ Ans ∣
      interpYes : 𝟙 LV.◂ top (⊤ .fst 𝟙) ≤ (pull yes $ interpAns)
      interpNo : 𝟙 LV.◂ top (⊤ .fst 𝟙) ≤ (pull no $ interpAns)

  module Reindex
    {Σ : Signature} 
    {M N : CBPVModel Σ}
    (F : CBPVMorphism M N)
    (L : Logic N) where 

    private 
      module M = CBPVModel M
      module N = CBPVModel N
      module L = Logic L


    open CBPVMorphism F

    VH' : Functor (M.V ^op) (POSET ℓ-zero ℓ-zero) 
    VH' = L.VH ∘F (FV ^opF)

    CH' : Functor (M.C ^op) (POSET ℓ-zero ℓ-zero) 
    CH' = L.CH ∘F (FC ^opF)

    Sq' : NatTrans 
      (FORGET ∘F M.O)  
      (Hom^op ∘F (VH' ×F ((CH' ^opF) ∘F to^op^op)))
    Sq' = 
      seqTrans (FORGET ∘ʳ FO) (
      seqTrans F-assocl (
      seqTrans (L.Sq ∘ˡ ((FV ^opF) ×F FC)) 
      dumb ))  where 

      dumb : NatTrans
        ((Hom^op ∘F (L.VH ×F ((L.CH ^opF) ∘F to^op^op))) ∘F ((FV ^opF) ×F FC))
        (Hom^op ∘F ((L.VH ∘F (FV ^opF)) ×F (((L.CH ∘F (FC ^opF)) ^opF) ∘F to^op^op)))
      dumb .N-ob x z = z
      dumb .N-hom f = refl

    reindex : Logic M 
    reindex .Logic.VH = VH'
    reindex .Logic.CH = CH'
    reindex .Logic.Sq = Sq'
    reindex .Logic.pullOp {A}{B} op args P Q dargs = goal where 
      private 
        module VH' = HDSyntax VH'
        module VH = HDSyntax L.VH
        
      pull : {A : M.V .ob}{B : M.C .ob}(M' : M.O'[ A , B ])  
        → MonFun (CH' .F-ob  B .fst) (VH' .F-ob A .fst) 
      pull {A} {B} M = Sq' .N-ob (A , B) M

      opN : N.O'[ F-ob (FV ^opF) A , F-ob (FC ^opF) B ] 
      opN = N.O .F-ob ((F-ob (FV ^opF) A) , (F-ob (FC ^opF) B)) .interp op (λ z → N-ob FO (A , B) .carmap (args z))

      opM : N.O'[ F-ob (FV ^opF) A , F-ob (FC ^opF) B ]
      opM = N-ob FO (A , B) .carmap (M.O .F-ob (A , B) .interp op args)

      have : F-ob (FV ^opF) A VH.◂ P ≤ (L.pull opN  $ Q)
      have = L.pullOp op (λ z → N-ob FO (A , B) .carmap (args z)) P Q dargs

      subgoal' : opN ≡ opM
      subgoal' = sym (N-ob FO (A , B) .pres  op args )

      subgoal : L.pull opN ≡ pull (M.O[ A , B ] .interp op args)
      subgoal = cong L.pull subgoal'

      goal : A VH'.◂ P ≤ (pull (M.O[ A , B ] .interp op args) $ Q)
      goal = VH'.seq have (VH'.eqTo≤ ((cong (λ h → MonFun.f h Q ) subgoal)))


  module Convert {C : Category _ _} (F : Functor (C ^op) (POSET _ _ )) where 
    open HDSyntax F  

    Cᴰ : Categoryᴰ C _ _ 
    ob[ Cᴰ ] = F∣_∣
    Cᴰ .Hom[_][_,_] {x}{y} f Fx Fy = x ◂ Fx ≤ f* f Fy
    Cᴰ .idᴰ = eqTo≤  (sym f*id)
    Cᴰ ._⋆ᴰ_ {f = f} {g} = seq* f g
    Cᴰ .⋆IdLᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
    Cᴰ .⋆IdRᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
    Cᴰ .⋆Assocᴰ _ _ _ = toPathP (isProp≤ _ _)
    Cᴰ .isSetHomᴰ = isProp→isSet isProp≤ 

  module ConvertLogic
    {Σ : Signature}
    (M : CBPVModel Σ)
    (L : Logic M) where 

    open import HyperDoc.Syntax
    open CBPVModel M 
    open Logic L
    
    Vᴰ : Categoryᴰ V _ _ 
    Vᴰ = Convert.Cᴰ VH

    Cᴰ : Categoryᴰ C _ _ 
    Cᴰ = Convert.Cᴰ CH
    
    module VL = HDSyntax VH 
    module CL = HDSyntax CH 
    
    open MonFun renaming (f to fun)

    Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) (ALGᴰ {Σ})
    Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .Carrierᴰ M = A VL.◂ P ≤ (pull M $ Q) , isProp→isSet VL.isProp≤
    Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .interpᴰ op args dargs = pullOp op args P Q dargs 
    Oᴰ .Functorᴰ.F-homᴰ {A , B} {A' , B'} {f , g} {P , Q} {P' , Q'} (P'≤f*P , Q≤g*Q') .carmapᴰ h P≤h*Q = 
      VL.seq  P'≤f*P (
      VL.seq (VL.mon* f P≤h*Q)  (
      VL.seq (VL.mon* f (pull h .isMon  Q≤g*Q')) (
      VL.eqTo≤ (sym (cong(λ h → h .fun Q') (funExt⁻ (Sq .N-hom (f , g)) h))))))
    Oᴰ .Functorᴰ.F-homᴰ {A , B} {A' , B'} {f , g} {P , Q} {P' , Q'} (P'≤f*P , Q≤g*Q') .presᴰ op args dargs = toPathP (VL.isProp≤ _ _)
    Oᴰ .Functorᴰ.F-idᴰ = toPathP (AlgHomᴰ≡Prop λ _ → VL.isProp≤)
    Oᴰ .Functorᴰ.F-seqᴰ _ _ = toPathP (AlgHomᴰ≡Prop λ _ → VL.isProp≤)

    OᴰBif : Bifunctorᴰ (ParFunctorToBifunctor O) (Vᴰ ^opᴰ) Cᴰ (ALGᴰ {Σ})
    OᴰBif = ParFunctorᴰToBifunctorᴰ Oᴰ

    Mᴰ : CBPVModelᴰ M 
    Mᴰ .CBPVModelᴰ.Vᴰ = Vᴰ
    Mᴰ .CBPVModelᴰ.Cᴰ = Cᴰ
    Mᴰ .CBPVModelᴰ.Oᴰ = Oᴰ

    open TypeStructure M

    module _ 
      (⊤ : L⊤.Has⊤ VH)
      (V⊤ : HasV𝟙 )  where
      open L⊤.HA 
      open L⊤.HAHom

      Vterm : Terminal' V
      Vterm .vertex = V⊤ .fst
      Vterm .element = tt
      Vterm .universal A .equiv-proof tt = {!   !}

      Vᴰtermⱽ : Terminalsⱽ Vᴰ
      Vᴰtermⱽ c .UniversalElementⱽ.vertexⱽ = top (⊤ .fst c)
      Vᴰtermⱽ c .UniversalElementⱽ.elementⱽ = tt
      Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ {y = c'}{f = f} .fst tt = VL.seq (top-top (⊤ .fst c')) (VL.eqTo≤ (sym (f-top (⊤ .snd f) )))
      Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ .snd .fst tt = refl
      Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ .snd .snd a = VL.isProp≤ _ a

      Vᴰtermᴰ : Terminalᴰ Vᴰ Vterm 
      Vᴰtermᴰ = Terminalⱽ→Terminalᴰ Vᴰ (Vᴰtermⱽ (TerminalNotation.𝟙 Vterm))


  module ModelSection 
    {Σ : Signature}
    {M N : CBPVModel Σ}
    (F : CBPVMorphism M N)
    (L : Logic N) where 

    open CBPVMorphism F
    private 
      module M = CBPVModel M 
      module N = CBPVModel N
      module L = Logic L
      module VH' = HDSyntax (L.VH ∘F (FV ^opF))
      module CH' = HDSyntax (L.CH ∘F (FC ^opF))

    open ConvertLogic N L
    module _ 
      (SV : Section FV Vᴰ) 
      (SC : Section FC Cᴰ) where 

      private 
        module SV = Section SV 
        module SC = Section SC
      
      SectionO : Type 
      SectionO = 
        ∀ 
          {A : ob M.V}
          {B : ob M.C}
          (M : M.O'[ A , B ]) → 
          ⟨ Oᴰ .F-obᴰ {FV .F-ob A , FC .F-ob B} (SV.F-obᴰ A , SC.F-obᴰ B) .Carrierᴰ (FO .N-ob (A , B) .carmap M) ⟩
        
    CBPVSection : Type 
    CBPVSection = Σ[ SV ∈ Section FV Vᴰ ] Σ[ SC ∈ Section FC Cᴰ ] SectionO SV SC

  CBPVGlobalSection :  {Σ : Signature}{M : CBPVModel Σ} → Logic M → Type 
  CBPVGlobalSection L = ModelSection.CBPVSection idCBPVMorphism L

  module Reconstruct 
    {Σ : Signature}
    {M : CBPVModel Σ}
    {L : Logic M}
    (GS : CBPVGlobalSection L) 
    where 

    open CBPVModel M 
    open Logic L 
    open Section
    open ConvertLogic M L
    open import Cubical.Categories.Constructions.TotalCategory

    TotalModel : CBPVModel Σ 
    TotalModel .CBPVModel.V = ∫C Vᴰ
    TotalModel .CBPVModel.C = ∫C Cᴰ
    TotalModel .CBPVModel.O = {!   !}


    GSFun : CBPVMorphism M {!  ∫C ? !} 
    GSFun = {!   !}

{- get from elim
  module Recursor (Σ : Signature)(M : CBPVModel Σ) where 
    open Syntax Σ
    open SyntacticModel Σ
    module M = CBPVModel M

    vty : VTy → ob M.V 
    vty 𝟙 = {!   !}
    vty (U x) = {!   !}

    cty : CTy → ob M.C 
    cty Ans = {!   !}

    vtm : {A A' : VTy} → A ⊢v A' → M.V [ vty A , vty A' ]
    vtm (subV V V') = M.V ._⋆_ (vtm V) (vtm V')
    vtm var = M.V .id
    vtm (subVIdl V i) = M.V .⋆IdL (vtm V) i
    vtm (subVIdr V i) =  M.V .⋆IdR (vtm V) i
    vtm (subVAssoc V₁ V₂ V₃ i) =  M.V .⋆Assoc (vtm V₁) (vtm V₂) (vtm V₃) i 
    vtm (isSet⊢v V₁ V₂ x y i j) = M.V .isSetHom (vtm V₁) (vtm V₂) (cong vtm x) (cong vtm y) i j
    vtm (thunk M) = {!   !}
    vtm (Uη i) = {!   !}
    vtm tt = {!   !}
    vtm (η𝟙 V₁ i) = {!   !}

    ktm : {B B' : CTy} → B ⊢k B' → M.C [ cty B , cty B' ]
    ktm (kcomp S S') = M.C ._⋆_ (ktm S) (ktm S')
    ktm hole = M.C .id
    ktm (kcompIdl S i) = M.C .⋆IdL (ktm S) i
    ktm (kcompIdr S i) = M.C .⋆IdR (ktm S) i
    ktm (kcompAssoc S S₁ S₂ i) = M.C .⋆Assoc (ktm S) (ktm S₁) (ktm S₂) i
    ktm (isSet⊢k S S' x y i j) =  M.C .isSetHom (ktm S) (ktm S') (cong ktm x) (cong ktm y) i j

    ctm' : {A : VTy}{B : CTy} → A ⊢c B → M.O'[ vty A , cty B ]
    ctm' (subC V M) = M.lcomp (vtm V) .carmap (ctm' M)
    ctm' (plug S M) = M.rcomp (ktm S) .carmap (ctm' M)
    ctm' (plugId {A}{B}{M} i) = M.lcompId {vty A}{cty B}{ctm' M} i
    ctm' (subCId {A}{B}{M} i) = M.rcompId {vty A}{cty B}{ctm' M} i
    ctm' (plugDist i) = {!   !}
    ctm' (subDist i) = {!   !}
    ctm' (plugSub i) = {!   !}
    ctm' (isSet⊢c M M₁ x y i i₁) = {!   !}
    ctm' (ops A B op args) = M.O[ vty A , cty B ] .interp op λ x → ctm' (args x)
    ctm' (opsSub V₁ op args i) = {!   !}
    ctm' (opsPlug S op args i) = {!   !}
    ctm' force = {!   !}
    ctm' yes = {!   !}
    ctm' no = {!   !}
    ctm' (Uβ i) = {!   !}
     
    ctm : {A : VTy}{B : CTy} → AlgHom (FreeCompAlg A B) M.O[ vty A , cty B ]
    ctm {A}{B} .carmap = ctm' {A}{B} 
    ctm .pres op args = {!   !}

    M-rec : CBPVMorphism SynModel M 
    M-rec .CBPVMorphism.FV .F-ob = vty
    M-rec .CBPVMorphism.FV .F-hom = vtm
    M-rec .CBPVMorphism.FV .F-id = refl
    M-rec .CBPVMorphism.FV .F-seq _ _ = refl
    M-rec .CBPVMorphism.FC .F-ob = cty
    M-rec .CBPVMorphism.FC .F-hom = ktm
    M-rec .CBPVMorphism.FC .F-id = refl 
    M-rec .CBPVMorphism.FC .F-seq _ _ = refl
    M-rec .CBPVMorphism.FO .N-ob (A , B) = ctm {A}{B}
    M-rec .CBPVMorphism.FO .N-hom _ = AlgHom≡ (funExt λ M → {!   !})
-}
  module Eliminator (Σ : Signature) where 
    open Syntax Σ
    open SyntacticModel Σ
    open Section
    
    module _ (L : Logic SynModel) where

      open ConvertLogic SynModel L
      open Logic L
      module LV = HDSyntax VH
      module LC = HDSyntax CH
      open TypeStructure SynModel
        

      module _ 
        (⊤ : L⊤.Has⊤ VH)
        (V⊤ : HasV𝟙 )
        (interpGen : InterpGen L ⊤ )
         where

        open L⊤.HA 
        
        open InterpGen interpGen
        
        mutual
          vty : (A : VTy) → LV.F∣ A ∣
          vty 𝟙 = top (⊤ .fst 𝟙)
          vty (U B) = pull force $ cty B

          cty : (B : CTy) → LC.F∣ B ∣
          cty Ans = interpAns


        mutual
          vtm-thunk : ∀ {A  B} → (M : A ⊢c B) →  A LV.◂ vty A ≤ LV.f* (thunk M) (pull force $ cty B) 
          vtm-thunk {A}{B} M = 
            LV.seq (ctm M) (
            LV.eqTo≤ (cong (λ h → MonFun.f (pull h) (cty B)) (sym Uβ ∙ sym plugId)
              ∙ cong (λ h → h .MonFun.f (cty B)) (pullLComp (thunk M) force))) 

          ctm-subC : ∀{A A' B}(V : A ⊢v A')(M : A' ⊢c B) →  A LV.◂ vty A ≤ (pull (subC V M) $ cty B)
          ctm-subC {A}{A'}{B} V M = subst (λ h → A LV.◂ vty A ≤ (pull h $ cty B)) plugId have where 
            have : A LV.◂ vty A ≤ (pull (plug hole (subC V M)) $ cty B)
            have = OᴰBif .Bif-homLᴰ  (vtm V) (cty B) .carmapᴰ M (ctm M)

          ctm-plug : ∀{A B B'}(S : B ⊢k B')(M : A ⊢c B) → A LV.◂ vty A ≤ (pull (plug S M) $ cty B')
          ctm-plug {A}{B}{B'} S M = subst (λ h → A LV.◂ vty A ≤ (pull h $ cty B')) (cong₂ plug refl subCId) have where 
            have : A LV.◂ vty A ≤ (pull (plug S (subC var M)) $ cty B') 
            have = OᴰBif .Bif-homRᴰ (vty A) (ktm S) .carmapᴰ M (ctm M)

          vtm : {A A' : VTy} → (V : A ⊢v A') → A LV.◂ vty A ≤ LV.f* V (vty A')
          vtm (subV V V') = Vᴰ ._⋆ᴰ_  (vtm V) (vtm V')
          vtm var = Vᴰ .idᴰ
          vtm (subVIdl V i) = Vᴰ .⋆IdLᴰ (vtm V) i
          vtm (subVIdr V i) = Vᴰ .⋆IdRᴰ (vtm V) i
          vtm (subVAssoc V₁ V₂ V₃ i) = Vᴰ .⋆Assocᴰ (vtm V₁) (vtm V₂) (vtm V₃) i
          vtm (isSet⊢v V V' x y i j) = 
            isOfHLevel→isOfHLevelDep 2 
              (λ x → Vᴰ .isSetHomᴰ) 
              (vtm V) (vtm V') 
              (cong vtm x) (cong vtm y) 
              (isSet⊢v V V' x y) i j

          vtm (thunk M) = vtm-thunk M
          vtm (Uη {A}{B}{V} i) = 
            isProp→PathP 
              ((λ i → LV.isProp≤{q = LV.f* (Uη i) (pull force $ cty B)})) 
              (vtm-thunk (subC' V force')) 
              (vtm V) 
              i
          vtm tt = LV.seq (top-top (⊤ .fst _)) (LV.eqTo≤ (sym (L⊤.HAHom.f-top (⊤ .snd tt))))
          vtm (η𝟙 {A} V i) = 
            VL.eq*PathP (η𝟙 {A} V) 
              (LV.seq (top-top (⊤ .fst _)) (LV.eqTo≤ (sym (L⊤.HAHom.f-top (⊤ .snd tt))))) 
              (vtm V) 
              i
      

          ktm : {B B' : CTy} → (S : B ⊢k B') → B LC.◂ cty B ≤ LC.f* S (cty B')
          ktm (kcomp S S') = Cᴰ ._⋆ᴰ_  (ktm S) (ktm S')
          ktm hole = Cᴰ .idᴰ
          ktm (kcompIdl S i) = Cᴰ .⋆IdLᴰ (ktm S) i
          ktm (kcompIdr S i) = Cᴰ .⋆IdRᴰ (ktm S) i
          ktm (kcompAssoc S₁ S₂ S₃ i) = Cᴰ .⋆Assocᴰ (ktm S₁) (ktm S₂) (ktm S₃) i
          ktm (isSet⊢k S S' x y i j) = 
            isOfHLevel→isOfHLevelDep 2 
              (λ x → Cᴰ .isSetHomᴰ) 
              (ktm S) (ktm S') 
              (cong ktm x) (cong ktm y) 
              (isSet⊢k S S' x y) i j

          {-# TERMINATING #-}
          -- Idk why.. but this termination pragma is needed for plugDist
          -- which is just showing that the PathP is a prop.. 
          -- there should be NO interesting recursion in the proof of equality
          -- need to fix
          ctm : ∀{A B} → (M : A ⊢c B) → A LV.◂ vty A ≤ (pull M $ cty B)
          ctm (subC V M) = ctm-subC V M 
          ctm (plug S M) = ctm-plug S M
          ctm (plugId {A}{B}{M} i) = 
            isProp→PathP 
              (λ i → LV.isProp≤{q = (pull (plugId i) $ cty B)})
              (ctm-plug hole M) 
              (ctm M) 
              i
          ctm (subCId {A}{B}{M} i) = 
            isProp→PathP  
              (λ i → LV.isProp≤{q = (pull (subCId i) $ cty B)}) 
              (ctm-subC var M)
              (ctm M) 
              i
          ctm (plugDist {A}{A'}{B}{B'}{S}{S'}{M} i) = 
            isProp→PathP 
              (λ i → LV.isProp≤{q = (pull (plugDist i) $ cty B')}) 
              (ctm-plug S' (plug S M)) 
              (ctm-plug (kcomp S S') M)
              i
          ctm (subDist {A}{A'}{A''}{B}{V}{V'}{M} i) = 
            isProp→PathP 
              (λ i → LV.isProp≤{q = (pull (subDist i) $ cty B)}) 
              (ctm-subC V (subC V' M)) 
              (ctm-subC (subV V V') M)
              i
          ctm (plugSub {A}{A'}{B}{B'}{V}{M}{S} i) =           
            isProp→PathP 
              (λ i → LV.isProp≤{q = (pull (plugSub i) $ cty B')}) 
              (ctm-subC V (plug S M)) 
              (ctm-plug S (subC V M))
              i
          ctm (isSet⊢c M M' x y i j) = 
              isOfHLevel→isOfHLevelDep 2 
                (λ x → isProp→isSet VL.isProp≤) 
                (ctm M) (ctm M') 
                (cong ctm x) (cong ctm y) 
                (isSet⊢c M M' x y) i j 

          ctm (ops A B op args) = pullOp op args (vty A) (cty B) (λ x → ctm (args x))
          ctm (opsSub {A}{A'}{B} V op args i) = 
            isProp→PathP 
              (λ i → LV.isProp≤{q = (pull (opsSub V op args i) $ cty B)}) 
              (ctm-subC V (ops A' B op args))
              (pullOp op (λ x → subC V (args x)) (vty A) (cty B) (λ x → ctm-subC V (args x)))
              i
          ctm (opsPlug {A}{B}{B'} S op args i) = 
            isProp→PathP 
              ((λ i → LV.isProp≤{q = (pull (opsPlug S op args i) $ cty B')}))
              (ctm-plug S (ops A B op args))
              (pullOp op (λ x → plug S (args x)) (vty A) (cty B')(λ x → ctm-plug S (args x)))
              i
          ctm force = LV.id⊢
          ctm yes = interpYes
          ctm no = interpNo
          ctm (Uβ {A}{B}{M} i) = 
            isProp→PathP 
              ((λ i → LV.isProp≤{q = (pull (Uβ i) $ cty B)})) 
              (ctm-subC (thunk M) force) 
              (ctm M) 
              i

        SV : Section Id Vᴰ 
        SV .F-obᴰ = vty
        SV .F-homᴰ = vtm
        SV .F-idᴰ = VL.isProp≤  _ _
        SV .F-seqᴰ _ _ = VL.isProp≤  _ _

        SC : Section Id Cᴰ 
        SC .F-obᴰ = cty
        SC .F-homᴰ = ktm
        SC .F-idᴰ = CL.isProp≤  _ _
        SC .F-seqᴰ _ _ = CL.isProp≤  _ _

        M-elim : CBPVGlobalSection L
        M-elim .fst = SV
        M-elim .snd .fst = SC
        M-elim .snd .snd = ctm

  module LocalElim 
    (Σ : Signature) 
    (N : CBPVModel Σ)
    (L : Logic N)
    (⊤ : L⊤.Has⊤ (Logic.VH L))
    (V⊤ : TypeStructure.HasV𝟙 N) where

    open Syntax Σ
    open SyntacticModel Σ

    module _ (F : CBPVMorphism SynModel N) where
      
      open Reindex F L 
      open ModelSection
      open CBPVMorphism F
      open TypeStructure

      open ConvertLogic N L

      LM : Logic SynModel
      LM = reindex

      open Eliminator Σ 
            
      module LMHV = HDSyntax (Logic.VH LM)
      module LMHC = HDSyntax (Logic.CH LM)

      pres⊤ : L⊤.Has⊤ (Logic.VH LM) 
      pres⊤ .fst = λ c → ⊤ .fst (F-ob (FV ^opF) c)
      pres⊤ .snd = λ f → ⊤ .snd (F-hom (FV ^opF) f)

      module _ (interp : InterpGen LM pres⊤) where

        M-elim' : CBPVGlobalSection LM
        M-elim' = M-elim LM pres⊤ (SyntacticModel.has𝟙 Σ) interp
        
        FSV : Section FV Vᴰ
        FSV = GlobalSectionReindex→Section Vᴰ FV convert where 
          convert : GlobalSection (reindexᴰ Vᴰ FV)
          convert .Section.F-obᴰ = M-elim' .fst .Section.F-obᴰ
          convert .Section.F-homᴰ = M-elim' .fst .Section.F-homᴰ
          convert .Section.F-idᴰ = LMHV.isProp≤ _ _
          convert .Section.F-seqᴰ _ _ = LMHV.isProp≤ _ _

        FSC : Section FC Cᴰ 
        FSC = GlobalSectionReindex→Section Cᴰ FC convert where 
          convert : GlobalSection (reindexᴰ Cᴰ FC)
          convert .Section.F-obᴰ = M-elim' .snd .fst .Section.F-obᴰ
          convert .Section.F-homᴰ = M-elim' .snd .fst .Section.F-homᴰ
          convert .Section.F-idᴰ = LMHC.isProp≤ _ _
          convert .Section.F-seqᴰ _ _ = LMHC.isProp≤ _ _ 

        M-elim-local : CBPVSection F L 
        M-elim-local .fst = FSV
        M-elim-local .snd .fst = FSC
        M-elim-local .snd .snd = M-elim' .snd .snd


  module BoopExample where 

    data Boop : Type where 
      boop : Boop

    Σb : Signature
    Σb .Op = Boop
    Σb .arity boop = 1

    M : CBPVModel Σb
    M .CBPVModel.V = SET _
    M .CBPVModel.C = ALG Σb
    M .CBPVModel.O .F-ob (A , B) .Carrier = (SET _)[ A , B .Carrier ] , (SET _) .isSetHom
    M .CBPVModel.O .F-ob (A , B) .interp boop arg a = B .interp boop λ x → arg x a
    M .CBPVModel.O .F-hom (f , h) .carmap g = λ z → h .carmap (g (f z))
    M .CBPVModel.O .F-hom (f , h) .pres boop arg = funExt λ a → h .pres boop λ x → arg x (f a)
    M .CBPVModel.O .F-id = AlgHom≡ refl
    M .CBPVModel.O .F-seq _ _ = AlgHom≡ refl

    module M' = CBPVModel M
    
    open import HyperDoc.Logics.SetPred
    open import Cubical.Foundations.Powerset
    open import Cubical.Functions.Logic hiding(⊥ ; inl ; inr)
    
    SubAlg : {Σ : Signature} → Alg Σ → Type
    SubAlg {Σ} A = Σ[ P ∈ ℙ ⟨ Carrier A ⟩  ] 
      ((op : Op Σ) → (args : Fin (arity Σ op) → 
        Σ[ a ∈ ⟨ Carrier A ⟩ ] a ∈ P ) → interp A op (λ i → args i .fst) ∈ P)


    subAlgPo : ob (ALG Σb) → ob (POSET  _ _) 
    subAlgPo A .fst .fst = SubAlg A
    subAlgPo A .fst .snd ._≤_ P Q = P .fst ⊆ Q .fst
    subAlgPo A .fst .snd .isPreorder .IsPreorder.is-prop-valued P Q = ⊆-isProp (P .fst)(Q .fst)
    subAlgPo A .fst .snd .isPreorder .IsPreorder.is-refl P = ⊆-refl (P .fst)
    subAlgPo A .fst .snd .isPreorder .IsPreorder.is-trans P Q R = ⊆-trans (P .fst) (Q .fst) (R .fst)
    -- this follows from antisym in ℙ
    subAlgPo A .snd = {!!}


    CH' : Functor ((ALG Σb) ^op) (POSET ℓ-zero ℓ-zero)
    CH' .F-ob = subAlgPo
    CH' .F-hom f .MonFun.f (P , clP) .fst a = P (f .carmap a)
    CH' .F-hom f .MonFun.f (P , clP) .snd = {!   !}
    CH' .F-hom f .MonFun.isMon = λ z x₂ → z (f .carmap x₂)
    CH' .F-id = eqMon _ _ {!   !}
    CH' .F-seq = {!   !}
 
    L : Logic M 
    L .Logic.VH = Pred
    L .Logic.CH = CH'
    L .Logic.Sq .N-ob (A , B) M .MonFun.f (Q , clQ) a = Q (M a)
    L .Logic.Sq .N-ob (A , B) M .MonFun.isMon Q a = Q (M a)
    L .Logic.Sq .N-hom f = refl
    L .Logic.pullOp boop arg P Q prf a Pa = Q .snd boop (λ z → arg z a , prf z a Pa)

    open SyntacticModel Σb
    open Syntax Σb
    module Syn =  CBPVModel SynModel

    -- Global Section
    F : CBPVMorphism SynModel M 
    F .CBPVMorphism.FV = V [ 𝟙 ,-]
    F .CBPVMorphism.FC = Syn.O[ 𝟙 ,-]
    F .CBPVMorphism.FO .N-ob (A , B) .carmap M V = subC V M
    F .CBPVMorphism.FO .N-ob (A , B) .pres boop arg = funExt λ V → opsSub V boop arg
    F .CBPVMorphism.FO .N-hom (V , S) = AlgHom≡ (funExt λ M → funExt λ W → plugSub ∙ cong₂ plug refl (subDist ∙ sym subCId))

    top' : L⊤.Has⊤ Pred
    top' .fst X = record { top = λ x → ⊤ ; top-top = λ {P} x _ → tt* }
    top' .snd f .L⊤.HAHom.f-top = refl

    unit : TypeStructure.HasV𝟙 M
    unit .fst = Unit , isSetUnit
    unit .snd .trans .N-ob c x = tt
    unit .snd .trans .N-hom _ _ _ _  = refl
    unit .snd .nIso x .fst = λ _ _ → tt
    unit .snd .nIso x .snd .fst tt = refl
    unit .snd .nIso x .snd .snd a  = funExt λ x₁ i → tt

    open LocalElim Σb M L top' unit 
        
    boop' : 𝟙 ⊢c Ans → 𝟙 ⊢c Ans 
    boop' M = ops 𝟙 Ans boop λ {zero  → M}

    bebop : ℕ → 𝟙 ⊢c Ans → 𝟙 ⊢c Ans 
    bebop zero M = M
    bebop (suc n) M = boop' (bebop n M)

    property' : 𝟙  ⊢c Ans → Type 
    property' M = Σ[ n ∈ ℕ ] ((M ≡ bebop n yes) ⊎ (M ≡ bebop n no))

    property : ℙ (𝟙  ⊢c Ans)
    property M = ∥ property' M ∥₁ , squash₁

    closed : (M : 𝟙 ⊢c Ans ) → M ∈ property → boop' M ∈ property 
    closed M = hmap goal where 
      goal : property' M → property' (boop' M)
      goal (n , inl x) = (suc n) , (inl (cong boop' x))
      goal (n , inr x) = (suc n) , (inr (cong boop' x))

    int : InterpGen (LM F) (pres⊤ F) 
    int .InterpGen.interpAns .fst = property
    int .InterpGen.interpAns .snd boop M =  goal where 
      have : 𝟙 ⊢c Ans 
      have = M zero .fst 

      have' : have ∈ property 
      have' = M zero .snd

      dumb : ops 𝟙 Ans boop (λ i → M i .fst) ≡ boop' have
      dumb = cong (λ h → ops 𝟙 Ans boop h) (funExt λ {zero → refl})

      goal : ops 𝟙 Ans boop (λ i → M i .fst) ∈ property 
      goal = subst (λ x → x ∈ property) (sym dumb) (closed have have')
    int .InterpGen.interpYes V tt* = ∣ (0 , (inl (cong₂ subC (sym (η𝟙 V) ∙ η𝟙 var) refl ∙ subCId))) ∣₁
    int .InterpGen.interpNo V tt* = ∣ (0 , (inr (cong₂ subC (sym (η𝟙 V) ∙ η𝟙 var) refl ∙ subCId))) ∣₁

    open ModelSection F L 
    open Section

    LR : CBPVSection
    LR = M-elim-local F int

    theorem : ∀ (M : 𝟙 ⊢c Ans) → ∥ (Σ[ n ∈ ℕ ] ((M ≡ bebop n yes) ⊎ (M ≡ bebop n no))) ∥₁ 
    theorem M = subst (λ h → h ∈ property) subCId (LR .snd .snd M var tt*)
