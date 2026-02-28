{-# OPTIONS --type-in-type #-}
-- this is for hacking, i dont care
-- do not read for your own sanity.. 
-- im using this as a blackboard to check my paper math
module HyperDoc.Algebras where 

  open import Cubical.Foundations.Prelude hiding (subst; _∧_)
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
  open import HyperDoc.Lib
  open import Cubical.Relation.Binary.Preorder
  open PreorderStr

  open Category
  open Functor
  open NatTrans  



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

  subst :
    {Σ : Signature} {n m : ℕ} →
    (Fin n → Term Σ m) →
    Term Σ n →
    Term Σ m
  subst σ (var i)      = σ i
  subst σ (app o args) =
    app o (λ j → subst σ (args j))

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

  open import Cubical.Foundations.Powerset
  open import Cubical.Functions.Logic hiding(⊥)

  SubAlg : {Σ : Signature} → Alg Σ → Type
  SubAlg {Σ} A = Σ[ P ∈ ℙ ⟨ Carrier A ⟩  ] 
               ((op : Op Σ) → (args : Fin (arity Σ op) → Σ[ a ∈ ⟨ Carrier A ⟩ ] a ∈ P ) → interp A op (λ i → args i .fst) ∈ P)
               --  interp A op (λ i → xs i) ∈ P)

  isAlg : Signature → hSet _ → Type 
  isAlg Σ X =  (op : Op Σ) → (Fin (arity Σ op) → ⟨ X ⟩) → ⟨ X ⟩ 

    -- SubAlg {Σ} (record { Carrier = P .fst .fst , {!   !} ; interp = algP })

  record DAlg (Σ : Signature)(A : Alg Σ) : Type where 
    field 
      DCar : (X : ⟨ A .Carrier ⟩ ) → hSet _
      interpᴰ : 
        (op : Op Σ)
        (args : Fin (arity Σ op) → ⟨ A. Carrier ⟩)
        (dargs : (x : Fin (arity Σ op)) → ⟨ DCar (args x) ⟩) → 
        ⟨ DCar (A .interp op args) ⟩
  open DAlg


  TotalAlg : (Σ : Signature)(A : Alg Σ)(D : DAlg Σ A) → Alg Σ
  TotalAlg Σ A D .Carrier = (Σ[ X ∈ ⟨ A .Carrier ⟩ ] ⟨ D .DCar X ⟩) , {!   !}
  TotalAlg Σ A D .interp op args = (A .interp op (λ x → args x .fst)) , (D .interpᴰ op ((λ x → args x .fst)) ((λ x → args x .snd)))
  

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

  open Theory
  open Equation
  open Model


  -- ah.. but can you ever construct an element of this type?
  -- only if the signature has a nullay operation
  -- see FreeOn .. which equips a set X with this structure
  data FreeAlg' (Σ : Signature) : Type where 
    ops : (o : Op Σ) → ((Fin (arity Σ o) → FreeAlg' Σ)) → FreeAlg' Σ

  FreeAlg : (Σ : Signature) → Alg Σ 
  FreeAlg Σ .Carrier = FreeAlg' Σ , {!   !}
  FreeAlg Σ .interp = ops


{-}
  data FreeModel' (T : Theory) : Type where 
    ops : (o : Op (T . Sig)) → ((Fin (arity (T .Sig) o) → FreeModel' T)) → FreeModel' T
    eqs : (e : Eq T)(env : Fin (ax T e .ctx) → FreeModel' T) → 
      eval (record { Carrier = FreeModel' T ; interp = ops }) (lhs (ax T e)) env 
        ≡ 
      eval (record { Carrier = FreeModel' T ; interp = ops }) (rhs (ax T e)) env  

  FreeModel : (T : Theory) → Model T 
  FreeModel T .alg .Carrier = FreeModel' T
  FreeModel T .alg .interp = ops
  FreeModel T .sound = eqs

 
-}
  boopTheory : Theory 
  boopTheory .Sig .Op = Unit
  boopTheory .Sig .arity tt = 1
  boopTheory .Eq = ⊥
  boopTheory .ax ()



  record AlgHom {Sig : Signature} (M N : Alg Sig) : Type where 
    field 
      carmap : ⟨ M .Carrier ⟩  → ⟨ N .Carrier ⟩ 
      pres : ∀ (op : Sig .Op)(args : Fin (Sig .arity op) → ⟨ M .Carrier ⟩ ) 
        → carmap (interp M op args) ≡ interp N op λ x → carmap (args x)

  open AlgHom

  isAlgHom : {Sig : Signature}{M N : Alg Sig}→  (⟨ M .Carrier ⟩  → ⟨ N .Carrier ⟩)  → Type 
  isAlgHom {Sig} {M} {N} f = ∀ (op : Sig .Op)(args : Fin (Sig .arity op) → ⟨ M .Carrier ⟩ ) 
        → f (interp M op args) ≡ interp N op λ x → f (args x)

  recAlg : {Σ : Signature} → (A : Alg Σ) → AlgHom (FreeAlg Σ) A 
  recAlg {Σ} A .carmap = go where 
    go : FreeAlg' Σ → ⟨ A .Carrier ⟩  
    go (ops op args) = A .interp op λ x → go (args x)
  recAlg A .pres _ _ = refl

{-}
  recMod : {T : Theory} → (M : Model T) → AlgHom (FreeModel T .alg) (M .alg) 
  recMod {T} M .carmap = go where 
    go : FreeModel' T → M .alg .Carrier
    go (ops o args) = M .alg .interp o λ x → go (args x)
    go (eqs e env i) = refl i
  recMod {T} M .pres _ _ = refl
-}
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

  AlgCat : Signature → Category (ℓ-suc ℓ-zero) ℓ-zero 
  AlgCat S .ob = Alg S
  AlgCat S .Hom[_,_] = AlgHom
  AlgCat S .id = idHom
  AlgCat S ._⋆_ = _⋆AlgHom_
  AlgCat S .⋆IdL _ = AlgHom≡ refl
  AlgCat S .⋆IdR _ = AlgHom≡ refl
  AlgCat S .⋆Assoc _ _ _ = AlgHom≡ refl
  AlgCat S .isSetHom = {!   !}

  open Model 
  ModelCat : Theory → Category (ℓ-suc ℓ-zero) ℓ-zero 
  ModelCat T .ob = Model T
  ModelCat T .Hom[_,_] M N = AlgHom (M .alg) (N .alg)
  ModelCat T .id = idHom
  ModelCat T ._⋆_ = _⋆AlgHom_
  ModelCat T .⋆IdL _ = AlgHom≡ refl
  ModelCat T .⋆IdR _ = AlgHom≡ refl
  ModelCat T .⋆Assoc _ _ _ = AlgHom≡ refl
  ModelCat T .isSetHom = {!   !}

  open import Cubical.Categories.Instances.Sets

  UF : {T : Theory} → Functor (ModelCat T) (SET _) 
  UF {T} .F-ob M = M .alg .Carrier 
  UF {T} .F-hom f = f .carmap
  UF {T} .F-id = refl
  UF {T} .F-seq _ _ = refl

  -- want to equip a set X with the struture of the algebra
  data FreeOn (S : Signature)(X : Type) : Type where 
    inc : X → FreeOn S X
    ops : (o : Op S) → (Fin (arity S o) → FreeOn S X) → FreeOn S X

  data FreeModelOn (T : Theory)(X : Type) : Type where 
    inc : X → FreeModelOn T X
    ops : (o : Op (T . Sig)) → ((Fin (arity (T .Sig) o) → FreeModelOn T X)) → FreeModelOn T X
    eqs : (e : Eq T)(env : Fin (ax T e .ctx) → FreeModelOn T X) → 
      eval (record { Carrier = FreeModelOn T X , {!   !} ; interp = ops }) (lhs (ax T e)) env 
        ≡ 
      eval (record { Carrier = FreeModelOn T X , {!   !} ; interp = ops }) (rhs (ax T e)) env  

  FreeModel : (T : Theory)(X : Type) → Model T 
  FreeModel T X .alg .Carrier = FreeModelOn T X , {!   !}
  FreeModel T X .alg .interp = ops
  FreeModel T X .sound = eqs


  FreeModelMorphism' : {T : Theory}{X : Type}{M : Model T} → 
    (X → ⟨ M .alg .Carrier ⟩ ) → 
    FreeModelOn T X → ⟨ M .alg .Carrier ⟩  
  FreeModelMorphism' {T} {X} {M} f (inc x) = f x
  FreeModelMorphism' {T} {X} {M} f (ops o args) = 
    M .alg .interp o (λ arg → FreeModelMorphism' {T}{X}{M} f (args arg))
  FreeModelMorphism' {T} {X} {M} f (eqs e env i) = refl i

  FreeModelMorphism : {T : Theory}{X : Type}{M : Model T} → 
    (X → ⟨ M .alg .Carrier ⟩ ) → 
    (ModelCat T)[ FreeModel T X , M ] 
  FreeModelMorphism {T} {X} {M} gen .carmap = 
    FreeModelMorphism' {T}{X}{M} gen
  FreeModelMorphism {T} {X} {M} gen .pres _ _ = refl


  FreeModelMorphism! : {T : Theory}{X : Type}{M : Model T} → 
    {f g : (ModelCat T)[ FreeModel T X , M ]} → 
    (∀ x → f .carmap (inc x) ≡ g .carmap (inc x)) → 
    f ≡ g
  FreeModelMorphism! {T}{X}{M}{f}{g} prf = AlgHom≡ (funExt goal) where 
    goal : (x : FreeModelOn T X) → f .carmap x ≡ g .carmap x 
    goal (inc x) = prf x
    goal (ops o x) = f .pres o x ∙ (λ i → interp (M .alg) o (λ a → goal (x a) i)) ∙ sym (g .pres o x)
    goal (eqs e env i) = M .alg .Carrier .snd (f .carmap (eqs e env i)) (g .carmap (eqs e env i)) _ _  i


  FreeModelMorphism≡ : {T : Theory} {X : Type} {M : Model T} →
    (f : X → ⟨ M .alg .Carrier ⟩ )
    (x : X) → 
    FreeModelMorphism f .carmap (inc x) ≡ f x
  FreeModelMorphism≡ {T}{X}{M} f x = refl

  open import Cubical.Data.Bool using (Bool ; true ; false )

  -- boop signature

  data Boop : Type where 
    boop : Boop

  boopSig : Signature
  boopSig .Op = Boop
  boopSig .arity boop = 1
  
  -- the free (boop) algebra on bool
  _ : FreeOn boopSig Bool 
  _ = ops boop λ {zero → ops boop λ {zero → inc true}}

  -- FreeOn boopSig A ≅ ℕ × A 
  open import Cubical.Foundations.Isomorphism
  -- as types and algebras
 {-} open Iso renaming(ret to ret')

  yoy : (X : Type) → Iso (FreeOn boopSig X) (ℕ × X) 
  yoy X .fun = go where 
    go : FreeOn boopSig X → ℕ × X
    go (inc x) = 0 , x
    go (ops boop x) = (1 + res .fst) , (res .snd) where 
      res : ℕ × X 
      res = go (x zero)
  yoy X .inv = go where 
    go : ℕ × X → FreeOn boopSig X 
    go (zero , x) = inc x
    go (suc n , x) = ops boop λ {zero → go (n , x)}
  yoy X .sec = {!   !}
  yoy X .ret' = {!   !} -}

  -- see how this is much simplier than the general F' for any signature
  so : Functor (SET _) (AlgCat boopSig)
  so .F-ob (X , _) .Carrier = ℕ × X , {!   !}
  so .F-ob (X , _) .interp boop arg = let (n , x) = arg zero in (1 + n) , x
  so .F-hom f .carmap (n , x) = n , (f x)
  so .F-hom f .pres boop arg = refl
  so .F-id = AlgHom≡ refl
  so .F-seq _ _ = AlgHom≡ refl

  -- NO, look at FT, 
  fmap : {S : Signature}{X Y : Type} → (X → Y) → FreeOn S X → FreeOn S Y 
  fmap f (inc x) = inc (f x)
  fmap f (ops o args) = ops o (λ x → fmap f (args x))

  fmap-id :{S : Signature}{X : Type}(e : FreeOn S X) → fmap (λ z → z) e ≡ e
  fmap-id (inc x) = refl
  fmap-id (ops o args) i = ops o λ a → fmap-id (args a) i
    
  fmap-comp : {S : Signature}{X Y Z : Type}{f : X → Y }{g : Y → Z } → 
    (e : FreeOn S X) → fmap (λ z → g (f z)) e ≡ fmap g (fmap f e)
  fmap-comp (inc x) = refl
  fmap-comp {f = f}{g} (ops o args) i = ops o λ a → fmap-comp {f = f}{g}(args a) i

  F' : {S : Signature} → Functor (SET _) (AlgCat S)
  F' {S} .F-ob (X , _) .Carrier = FreeOn S X , {!   !}
  F' {S} .F-ob (X , _) .interp = ops
  F' {S} .F-hom {X}{Y} f .carmap = fmap f
  F' {S} .F-hom f .pres _ _ = refl
  F' {S} .F-id {X} = AlgHom≡ (funExt fmap-id)
  F' {S} .F-seq _ _ = AlgHom≡ (funExt fmap-comp)


  FT : {T : Theory} → Functor (SET _) (ModelCat T)
  FT {T} .F-ob X = FreeModel T ⟨ X ⟩
  FT {T} .F-hom {X}{Y} f = 
    FreeModelMorphism {T}{⟨ X ⟩} {FreeModel T ⟨ Y ⟩ } λ x → inc (f x)
  FT {T} .F-id {X} = FreeModelMorphism! {T}{⟨ X ⟩}{FreeModel T ⟨ X ⟩ } λ _ → refl
  FT {T} .F-seq {X}{Y}{Z} f g = FreeModelMorphism!{T}{⟨ X ⟩}{FreeModel T ⟨ Z ⟩ } λ _ → refl

  open import Cubical.Foundations.Isomorphism 
  open Iso renaming (ret to retract)
  
  adj : ∀ {T : Theory}{A : ob (SET _)}{B : Model T} → 
    Iso ((SET _)[ A , UF .F-ob B ]) ((ModelCat T)[ FreeModel T ⟨ A ⟩ , B ]) 
  adj {T}{A}{B} .fun f = FreeModelMorphism {T}{⟨ A ⟩}{B} f
  adj .inv f = λ z → f .carmap (inc z)
  adj {T}{A}{B} .sec b = FreeModelMorphism! {T}{⟨ A ⟩}{B} λ _ → refl
  adj .Iso.ret a = refl



  record CBPVModel (T : Theory) : Type (ℓ-suc ℓ-zero) where 
    field 
      V : Category ℓ-zero ℓ-zero 
      C : Category ℓ-zero ℓ-zero 
      O : Functor (V ^op ×C C) (ModelCat T) 

    O[_,-] : (v : ob V) → Functor C (ModelCat T)
    O[_,-] v = O ∘F rinj _ _ v

    O[-,_] : (c : ob C) → Functor (V ^op) (ModelCat T)
    O[-,_] c = O ∘F linj _ _ c

    O[_,_] : ob V → ob C → ob (ModelCat T)
    O[_,_] v c = O .F-ob (v , c)

    O'[_,_] : ob V → ob C → Type 
    O'[_,_] v c = ⟨ O .F-ob (v , c) .alg .Carrier ⟩ 

    lcomp : ∀{v v' c} → V [ v , v' ] → (ModelCat T)[ O[ v' , c ] , O[ v , c ] ]
    lcomp f = O .F-hom (f , (C .id))

    rcomp : ∀{v c c'} → C [ c , c' ] → (ModelCat T)[ O[ v , c ] , O[ v , c' ] ]
    rcomp g = O .F-hom ((V .id) , g)

    lrcomp : ∀{v v' c c'} → V [ v' , v ] → C [ c , c' ] → (ModelCat T)[ O[ v , c ] , O[ v' , c' ] ]
    lrcomp V S = O .F-hom (V , S)




  termP : ob (POSET _ _)
  termP .fst .fst = Unit
  termP .fst .snd ._≤_ = λ z z₁ → Unit
  termP .fst .snd .isPreorder .IsPreorder.is-prop-valued tt tt tt tt = refl
  termP .fst .snd .isPreorder .IsPreorder.is-refl = λ a → tt
  termP .fst .snd .isPreorder .IsPreorder.is-trans = λ a b c _ _ → tt
  termP .snd = {!   !}

  -- agsy mess
  _×P_ : ob (POSET _ _) → ob (POSET _ _) → ob (POSET _ _) 
  (P ×P Q) .fst .fst = P . fst .fst  × Q .fst .fst
  (P ×P Q) .fst .snd .PreorderStr._≤_ (p , q)(p' , q') = P .fst .snd ._≤_ p p' × Q .fst .snd ._≤_ q q'
  (P ×P Q) .fst .snd .isPreorder .IsPreorder.is-prop-valued ((p , q))(p' , q')= isProp× (IsPreorder.is-prop-valued (isPreorder (P .fst .snd)) p p') (IsPreorder.is-prop-valued (isPreorder (Q .fst .snd)) q q')
  (P ×P Q) .fst .snd .isPreorder .IsPreorder.is-refl = λ a →
      IsPreorder.is-refl (isPreorder (P .fst .snd)) (a .fst) ,
      IsPreorder.is-refl (isPreorder (Q .fst .snd)) (a .snd)
  (P ×P Q) .fst .snd .isPreorder .IsPreorder.is-trans = λ a b c z z₁ →
      IsPreorder.is-trans (isPreorder (P .fst .snd)) (a .fst) (b .fst)
      (c .fst) (z .fst) (z₁ .fst)
      ,
      IsPreorder.is-trans (isPreorder (Q .fst .snd)) (a .snd) (b .snd)
      (c .snd) (z .snd) (z₁ .snd)
  (P ×P Q) .snd = {!   !}

  ×Pⁿ' : (n : ℕ) → (Fin n → ob (POSET _ _ )) → ob (POSET _ _ )
  ×Pⁿ' zero args = termP
  ×Pⁿ' (suc n) args = args zero ×P (×Pⁿ' n (λ i → args (suc i)))

  ×Pⁿ : (n : ℕ) → ob (POSET _ _ ) → ob (POSET _ _ )
  ×Pⁿ n P = ×Pⁿ' n λ _ → P

  ×ⁿ : {A : Type} → (n : ℕ) → Type 
  ×ⁿ {A} zero = Unit
  ×ⁿ {A} (suc n) = A × ×ⁿ {A} n

  fⁿ :{A B : Type} → (n : ℕ) → (f : A → B) → ×ⁿ {A} n → ×ⁿ {B} n
  fⁿ zero f tt = tt
  fⁿ (suc n) f (x , xs) = f x , fⁿ n f xs

  dupⁿ : (n : ℕ) → (P : ob (POSET _ _ )) → (POSET _ _ )[ P , ×Pⁿ n P ]
  dupⁿ zero P = record { f = λ _ → tt ; isMon = λ {x} {y} _ → tt }
  dupⁿ (suc n) P .MonFun.f p = p , dupⁿ n P .MonFun.f p
  dupⁿ (suc n) P .MonFun.isMon = λ z → z , dupⁿ n P .MonFun.isMon z
  
  open MonFun renaming (f to mfun)


  par' : {P Q : ob (POSET _ _ )} → (n : ℕ)→ (Fin n → (POSET _ _ )[ P , Q ]) → (POSET _ _ )[ ×Pⁿ n P , ×Pⁿ n Q ] 
  par' zero f .MonFun.f = λ _ → tt
  par' zero f .MonFun.isMon = λ _ → tt
  par' (suc n) f .mfun (P , Ps) = (f zero .mfun P) , (par' n (λ i → f (suc i)) .mfun Ps)
  par' (suc n) f .isMon = λ z →
      f zero .isMon (z .fst) , par' n (λ i → f (suc i)) .isMon (z .snd)

  par : {P Q : ob (POSET _ _ )} → (n : ℕ) → (POSET _ _ )[ P , Q ] → (POSET _ _ )[ ×Pⁿ n P , ×Pⁿ n Q ] 
  par n f = par' n λ _ → f
  
  isAlgP : Signature → ob (POSET _ _ ) → Type 
  isAlgP Σ P = (op : Op Σ) → (POSET _ _ )[ ×Pⁿ (Σ .arity op) P , P ]

  AlgP : Signature → Type 
  AlgP Σ = Σ[ P ∈ ob (POSET _ _ ) ] (isAlgP Σ P)

  subPo : (P : ob (POSET _ _ )) → (pred :  ℙ (P .fst .fst)) →  ob (POSET _ _ ) 
  subPo P pred .fst .fst = Σ[ x ∈ P .fst .fst ] x ∈ pred
  subPo P pred .fst .snd ._≤_ = λ z z' → P .fst .snd ._≤_ (z .fst) (z' .fst)
  subPo P pred .fst .snd .isPreorder .IsPreorder.is-prop-valued = λ a b →
      IsPreorder.is-prop-valued (isPreorder (P .fst .snd)) (a .fst)
      (b .fst)
  subPo P pred .fst .snd .isPreorder .IsPreorder.is-refl = λ a → IsPreorder.is-refl (isPreorder (P .fst .snd)) (a .fst)
  subPo P pred .fst .snd .isPreorder .IsPreorder.is-trans = λ a b c →
      IsPreorder.is-trans (isPreorder (P .fst .snd)) (a .fst) (b .fst)
      (c .fst)
  subPo P pred .snd = {!   !}

  inc' : (P : ob (POSET _ _ )) → (pred :  ℙ (P .fst .fst)) → (POSET _ _ )[ (subPo P pred) ,  P ] 
  inc' P pred .mfun = λ z → z .fst
  inc' P pred .isMon = λ z → z

  SubAlgP : {Σ : Signature} → AlgP Σ → Type
  SubAlgP {Σ} (P , algP) =
    Σ[ S ∈ ℙ (P .fst .fst) ]  
      ((op : Op Σ) → (args : {! ×Pⁿ (arity Σ op) ?  !} ) → {!   !}) -- S ⊆ P
    --  ((op : Op Σ) →
     -- (args : ×Pⁿ (arity Σ op) S) →
     --   algP op args ∈ S)

  {- 
   SubAlg : {Σ : Signature} → Alg Σ → Type
  SubAlg {Σ} A = Σ[ P ∈ ℙ ⟨ Carrier A ⟩  ] 
               ((op : Op Σ) → (args : Fin (arity Σ op) → Σ[ a ∈ ⟨ Carrier A ⟩ ] a ∈ P ) → interp A op (λ i → args i .fst) ∈ P)
  
  Closed : (A : WriterAlg ℓ) → ℙ ⟨ A ⟩ → Type (ℓ-max ℓS ℓ)
  Closed A P = (w : ⟨ Char ⟩)(a : A .fst) → a ∈ P → A .snd w a ∈ P

  isPropClosed : (A : WriterAlg ℓ) → (P : ℙ (A .fst)) → isProp (Closed A P) 
  isPropClosed A P p q = funExt λ w → funExt λ a → funExt λ Pa → P (A .snd w a) .snd (p w a Pa) (q w a Pa)

  SubAlg : (A : WriterAlg ℓ) → Type (ℓ-max ℓS (ℓ-suc ℓ))
  SubAlg A = Σ[ P ∈ ℙ (A .fst) ] Closed A P

  module _ {B B' : WriterAlg ℓ} where
    pull : (ϕ : WriterHom B B') (Q : SubAlg B') → SubAlg B
    pull ϕ Q .fst b = Q .fst (ϕ .fst b)
    pull ϕ Q .snd c b Q⟨ϕb⟩ = substₚ (Q .fst) ∣ (ϕ .snd c b) ∣₁  (Q .snd c (ϕ .fst b) Q⟨ϕb⟩)

    subAlg≡ : {X Y : SubAlg B} → (X .fst ≡ Y .fst) → X ≡ Y
    subAlg≡ {X}{Y} prf = ΣPathP (prf , toPathP (isPropClosed B (Y .fst) _ (Y .snd))) 

    subAlg≡' : {X Y : SubAlg B} → ((b : B .fst) → ⟨ X .fst b ⇔ Y .fst b ⟩) → X ≡ Y
    -- subAlg≡' {X}{Y} prf = subAlg≡ (funExt λ b → ⇔toPath (prf b .fst)  (prf b .snd)) 5

  subAlgPo : ob (WRITERALG ℓ) → ob (POSET  (ℓ-max ℓS (ℓ-suc ℓ)) ℓ ) 
  subAlgPo A .fst .fst = SubAlg (A .fst)
  subAlgPo A .fst .snd ._≤_ P Q = P .fst ⊆ Q .fst
  subAlgPo A .fst .snd .isPreorder .IsPreorder.is-prop-valued P Q = ⊆-isProp (P .fst)(Q .fst)
  subAlgPo A .fst .snd .isPreorder .IsPreorder.is-refl P = ⊆-refl (P .fst)
  subAlgPo A .fst .snd .isPreorder .IsPreorder.is-trans P Q R = ⊆-trans (P .fst) (Q .fst) (R .fst)
  subAlgPo A .snd = {!   !}
  -}

  isAlgHomP : (Σ : Signature) → {P Q : ob (POSET _ _ )}{algP : isAlgP Σ P}{algQ : isAlgP Σ Q} → (POSET _ _ )[ P , Q ] → Type 
  isAlgHomP Σ {P}{Q}{algP}{algQ} f = 
    (op : Op Σ) → 
        MonComp (algP op) f 
      ≡ 
        MonComp (par (Σ .arity op) f) (algQ op)
  


  -- posets, but where every fiber has the algebra structure 
  -- and monotone functions are algebra homomorphisms
  POSETALG : Theory → Category _ _
  POSETALG T .ob = Σ[ P ∈ ob (POSET _ _ ) ] isAlgP (T .Sig) P
  POSETALG T .Hom[_,_] (P , algP) (Q , algQ) = Σ[ f ∈ (POSET _ _ )[ P , Q ] ] isAlgHomP (T .Sig) {P}{Q}{algP}{algQ} f
  POSETALG T .id .fst = MonId
  POSETALG T .id .snd op = eqMon _ _ {!   !} -- yes
  POSETALG T ._⋆_ (f , fhom) (g , ghom) .fst = (MonComp f g) 
  POSETALG T ._⋆_ (f , fhom) (g , ghom) .snd op = eqMon _ _ {!   !} -- yes
  POSETALG T .⋆IdL (f , fhom) = ΣPathP (((POSET _ _ ) .⋆IdL f) , {!   !}) -- should only have to show eq on underlying map
    -- (toPathP (funExt (λ op → (POSET _ _ ) .isSetHom {!   !} {!   !} {!   !} {!   !}))))
  POSETALG T .⋆IdR (f , fhom) = ΣPathP (((POSET _ _ ) .⋆IdR f) , {!   !})
  POSETALG T .⋆Assoc (f , fhom) (g , ghom) (h , hhom) = ΣPathP ( (POSET _ _ ) .⋆Assoc f g h , {!   !})
  POSETALG T .isSetHom = {!   !}

  open import Cubical.Categories.Constructions.FullSubcategory

  POSETALGCL : Theory → Category _ _ 
  POSETALGCL T = FullSubcategory (POSETALG T) 
    λ (P , algP) → 
      Σ[ S ∈ ℙ (P .fst .fst) ] 
        ((op : Op (T .Sig))(args : ×Pⁿ (T .Sig .arity op) (subPo P S) .fst .fst )  → 
          algP op .mfun (par (T .Sig .arity op) (inc' P  S) .mfun args) ∈ S)

  glue : (T : Theory) → Functor (POSETALG T ×C (POSETALG T ^op)) (ModelCat T)
  glue T .F-ob (PA , QA) .alg .Carrier = (POSET _ _ ) [ QA .fst , PA .fst ] , (POSET _ _ ) .isSetHom
  glue T .F-ob ((P , algP) , Q , algQ) .alg .interp op args = MonComp (MonComp (dupⁿ (arity (T .Sig) op) Q) (par' (arity (T .Sig) op) args)) (algP op)
  glue T .F-ob ((P , algP) , Q , algQ) .sound = {!   !} -- punt
  glue T .F-hom (f , h) .carmap g = MonComp (h .fst) (MonComp g (f .fst))
  glue T .F-hom (f , fhom) .pres op args = eqMon _ _ (funExt λ x → {!   !}) -- probably holds by monotonicity
  glue T .F-id = AlgHom≡ (funExt λ _ → eqMon _ _ refl)
  glue T .F-seq _ _ = AlgHom≡ (funExt λ _ → eqMon _ _ refl)


  sub : {T : Theory}{C : Category _ _ } → Functor (C ^op) (POSETALG T)
  sub {T} {C} .F-ob = {!   !}
  sub {T} {C} .F-hom = {!   !}
  sub {T} {C} .F-id = {!   !}
  sub {T} {C} .F-seq = {!   !}
  
  -- do we really want a natural transformation..? 
  -- this does not appear to be the correct structure
  record Logic {T : Theory}(M : CBPVModel T) : Type where 
    open CBPVModel M
    field 
      VH : Functor (V ^op) (POSETALG T)
      CH : Functor (C ^op) (POSETALGCL T)
      -- do we really want this to land in algebras..?
      Sq : NatTrans O ( glue T ∘F ((VH  ×F ((FullInclusion (POSETALG T) _ ^opF) ∘F (CH ^opF) ∘F to^op^op))))

  open import HyperDoc.Logics.SetPred


  -- if the hyperdoctrine has ∧ and ⊤ , we can use that to interpret the algebra
  -- (POSET _ _ )[ ×Pⁿ (Σ .arity op) P , P ]
  open import HyperDoc.Connectives.Connectives
  module _ (P : ob (POSET _ _ ))(has∧ : L∧.HA P)(has⊤ : L⊤.HA P) where 
    open L∧.HA has∧ renaming (_∧_ to _⋀_)
    open L⊤.HA has⊤ 


    and : (n : ℕ) → (POSET _ _ )[ ×Pⁿ n P , P ]
    and zero .mfun tt = top
    and zero .isMon = λ z →
        IsPreorder.is-refl (isPreorder (P .fst .snd)) (and zero .mfun _)
    and (suc n) .mfun (P , Ps) = P ⋀ and n .mfun Ps
    and (suc n) .isMon x≤y = and-mono (x≤y .fst) (and n .isMon (x≤y .snd))

  -- for boop, we could just return the given predicate since it is unary.
  -- but demonstratin and here
  test : Functor ((SET _) ^op) (POSETALG boopTheory)
  test .F-ob X = Pred .F-ob X ,  λ op → and {!   !} {!   !} {!   !} 1
  test .F-hom f .fst = record
    { f = λ z z₁ → fst (z (f z₁)) , z (f z₁) .snd
    ; isMon = λ {x = x₁} {y = y₁} z x₂ → z (f x₂)
    }
  test .F-hom f .snd tt = eqMon _ _ {!   !} 
    -- this is just the fact that ∧ is preserved by monotone functions.
    -- which we have as an assumption
  test .F-id = {!   !}
  test .F-seq = {!   !}

  -- more interesting example... 
  -- no.. 
  open import HyperDoc.Models.ManualWriter using (CL ;  𝓒 )
  test' : Functor ( 𝓒  ^op) (POSETALGCL boopTheory)
  test' .F-ob B .fst .fst = Pred .F-ob  ((B .fst .fst) , {!   !})
  test' .F-ob B .fst .snd = λ op →
      record
      { f = λ z z₁ → fst (z .fst z₁) , z .fst z₁ .snd
      ; isMon = λ {x} {y} z → z .fst
      }
  test' .F-ob B .snd = {! subAlgPo  !} , (λ tt args → {!   !})
  test' .F-hom = {!   !}
  test' .F-id = {!   !}
  test' .F-seq = {!   !}

{-}
  testL : Logic {boopTheory} {!   !}
  testL .Logic.VH = test
  testL .Logic.CH = test'
  testL .Logic.Sq .N-ob (A , B) .carmap M .mfun = {!   !}
  testL .Logic.Sq .N-ob (A , B) .carmap M .isMon = {!   !}
  testL .Logic.Sq .N-ob M .pres tt arg = eqMon _ _ {!   !}
  testL .Logic.Sq .N-hom = {!   !} 
  -}

   {-}
  subAlgPo : ob (WRITERALG ℓ) → ob (POSET  (ℓ-max ℓS (ℓ-suc ℓ)) ℓ ) 
  subAlgPo A .fst .fst = SubAlg (A .fst)
  subAlgPo A .fst .snd ._≤_ P Q = P .fst ⊆ Q .fst
  subAlgPo A .fst .snd .isPreorder .IsPreorder.is-prop-valued P Q = ⊆-isProp (P .fst)(Q .fst)
  subAlgPo A .fst .snd .isPreorder .IsPreorder.is-refl P = ⊆-refl (P .fst)
  subAlgPo A .fst .snd .isPreorder .IsPreorder.is-trans P Q R = ⊆-trans (P .fst) (Q .fst) (R .fst)
  subAlgPo A .snd = {!   !}
  -}

{-}
  Hom^op : Functor ((POSET _ _ ) ×C (POSET _ _ )^op) (SET _)
  Hom^op  .F-ob (P , Q) = (POSET _ _ ) [ Q , P ] , (POSET _ _ ) .isSetHom
  Hom^op .F-hom {(A , B)}{(A' , B')} (f , g) h = MonComp g (MonComp h f)
  Hom^op .F-id = funExt λ _ → eqMon _ _ refl
  Hom^op .F-seq _ _ = funExt λ _ → eqMon _ _ refl


  hrm :  {T : Theory}→ Functor ((POSET _ _ ) ×C (POSET _ _ )^op) (ModelCat T)
  hrm {T} .F-ob (P , Q) .alg .Carrier = (POSET _ _ ) [ Q , P ] , (POSET _ _ ) .isSetHom
  hrm {T} .F-ob (P , Q) .alg .interp op args = {!   !}
  hrm {T} .F-ob (P , Q) .sound = {!   !}
  hrm {T} .F-hom (f , g) .carmap h = MonComp g (MonComp h f)
  hrm {T} .F-hom (f , g) .pres op args = {!   !} -- eqMon _ _ (funExt {!   !})
  hrm {T} .F-id = AlgHom≡ (funExt λ _ → eqMon _ _ refl)
  hrm {T} .F-seq _ _ = AlgHom≡ (funExt λ _ → eqMon _ _ refl)


  again : {T : Theory}→ Functor (POSET ℓ-zero ℓ-zero ×C (POSET ℓ-zero ℓ-zero ^op)) (ModelCat T) 
  again {T} .F-ob (P , Q) .alg .Carrier = (POSET _ _ ) [ Q , P ] , (POSET _ _ ) .isSetHom
  again {T} .F-ob (P , Q) .alg .interp op args = {!   !}
  again {T} .F-ob (P , Q) .sound = {!   !}
  again {T} .F-hom = {!   !}
  again {T} .F-id = {!   !}
  again {T} .F-seq = {!   !}

  -- no.. missing structure
  AlgHyperdoc : Theory → Category _ _ → Type _ 
  AlgHyperdoc T C = 
    Σ[ F ∈ Functor (C ^op) (POSET _ _) ] 
    Σ[ algStr ∈ (∀(c : C .ob ) → isAlg (T .Sig) (F .F-ob  c .fst .fst , {!   !})) ]  
    (∀ {c c'}(f : C [ c , c' ]) → 
      isAlgHom {T .Sig}
        {record { Carrier = F .F-ob  c' .fst .fst , {!   !} ; interp = algStr c' }}
        {record { Carrier = F .F-ob  c .fst .fst , {!   !} ; interp = algStr c }} 
        (F .F-hom f .mfun))
  
  record Logic {T : Theory}(M : CBPVModel T) : Type where 
    open CBPVModel M
    field 
      VH : AlgHyperdoc T V
      CH : AlgHyperdoc T C
      Sq : NatTrans O ( {!   !} ∘F (((VH .fst) ×F (((CH .fst) ^opF) ∘F to^op^op))))
      {-}
      VH : Functor (V ^op) (POSET _ _)
      CH : Functor (C ^op) (POSET _ _)
      Sq : NatTrans O  (hrm ∘F ((VH ×F ((CH ^opF) ∘F to^op^op))))
      -}




  -- no, logical and is an 
  test : AlgHyperdoc boopTheory (SET _) 
  test .fst = Pred
  test .snd .fst X tt args = args zero -- or just logical and! when n-ary 
  test .snd .snd f tt args = refl

  open import HyperDoc.Models.ManualWriter using (CL ;  𝓒 )
  test' : AlgHyperdoc boopTheory 𝓒
  test' .fst = CL
  test' .snd .fst B tt arg = {!   !}
  test' .snd .snd = {!   !}

-}

{-}
  module uhg {T : Theory}(M : CBPVModel T)(L : Logic {T} M) where 
    open import HyperDoc.AsDisplayed  
    open import HyperDoc.Syntax
    open import Cubical.Categories.Displayed.Base
    open import Cubical.Categories.Displayed.Functor
    open import Cubical.Categories.Displayed.BinProduct 
    open import Cubical.Categories.Instances.Preorders.Monotone 


    open CBPVModel M
    open Logic L
    open Categoryᴰ
    open Functorᴰ
    open DAlg

    --module VL = HDSyntax (VH .fst) 
    -- module CL = HDSyntax (CH .fst) 

    Algᴰ : Categoryᴰ (ModelCat T) _ _ 
    ob[ Algᴰ ] A = DAlg (T .Sig) (A .alg)
    Algᴰ .Hom[_][_,_] = {!   !}
    Algᴰ .idᴰ = {!   !}
    Algᴰ ._⋆ᴰ_ = {!   !}
    Algᴰ .⋆IdLᴰ = {!   !}
    Algᴰ .⋆IdRᴰ = {!   !}
    Algᴰ .⋆Assocᴰ = {!   !}
    Algᴰ .isSetHomᴰ = {!   !}

    Vᴰ : Categoryᴰ V _ _
    Vᴰ = convert.Cᴰ (VH .fst) 

    Cᴰ : Categoryᴰ C _ _
    Cᴰ = convert.Cᴰ (CH .fst) 
-}

{-} 
{-}
    pull : {A : ob V}{B : ob C} → (M : O'[ A , B ]) → MonFun (CH .F-ob B .fst) (VH .F-ob A .fst) 
    pull {A}{B} M = Sq .N-ob (A , B) .carmap M

    Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) Algᴰ
    Oᴰ .F-obᴰ {A , B} (P , Q) .DCar o = (A VL.◂ P ≤ pull o .mfun Q) , isProp→isSet VL.isProp≤
    Oᴰ .F-obᴰ {A , B} (P , Q) .interpᴰ op args dargs = {! Sq .N-ob (A , B) .pres op args !}
    Oᴰ .F-homᴰ {(A , B)}{(A' , B')}{(f , g)}{(P , Q)}{(P' , Q')}(P'≤f*P , Q≤g*Q' ) = {!   !}
    Oᴰ .F-idᴰ = {!   !}
    Oᴰ .F-seqᴰ = {!   !}
-}
    
    {-
    
  Oᴰ :  Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) (SETᴰ (ℓ-max ℓP ℓP') ℓP'  )
  Oᴰ .F-obᴰ {(A , B)}(P , Q) o = (A VL.◂ P ≤ (Sq .N-ob (A , B) o .fun Q) ), isProp→isSet VL.isProp≤ 
  Oᴰ .F-homᴰ {(A , B)}{(A' , B')}{(f , g)}{(P , Q)}{(P' , Q')}(P'≤f*P , Q≤g*Q' ) o  P≤o*Q = 
    VL.seq  P'≤f*P (
    VL.seq (VL.mon* f P≤o*Q) (
    VL.seq (VL.mon* f (pull o .isMon  Q≤g*Q')) (
    VL.eqTo≤ (sym (cong(λ h → h .fun Q') (funExt⁻ (Sq .N-hom (f , g)) o))))))
  Oᴰ .F-idᴰ = toPathP (funExt λ _ → funExt λ _ → VL.isProp≤ _ _)
  Oᴰ .F-seqᴰ _ _ = toPathP (funExt λ _ → funExt λ _ → VL.isProp≤ _ _)
    -}

    {-

open import Cubical.Categories.NaturalTransformation
record Logic 
  {ℓV ℓV' ℓC ℓC' ℓP ℓP'  : Level}
  (M : Model ℓV ℓV' ℓC ℓC' (ℓ-max ℓP ℓP')) : Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓ-suc ℓP ∷ ℓ-suc ℓP' ∷ [])) where 
  open Model M
  field 
    VH : Functor (V ^op) (POSET ℓP ℓP')
    CH : Functor (C ^op) (POSET ℓP ℓP')
    Sq : NatTrans O (Hom^op ∘F (VH ×F ((CH ^opF) ∘F to^op^op)))
    -}
  -- example 



  open import HyperDoc.Effects.ManualWriter
  open Writer (Unit , isSetUnit)
{-}
  -- should this do anything ..?
  ex : CBPVModel boopTheory 
  ex .CBPVModel.V = SET _
  ex .CBPVModel.C = WRITERALG _
  ex .CBPVModel.O .F-ob (A , B) .alg .Carrier = ⟨ A ⟩ → ⟨ B .fst .fst ⟩  , ?
  ex .CBPVModel.O .F-ob (A , B) .alg .interp tt arg a = B .fst .snd tt (arg zero a)
  ex .CBPVModel.O .F-ob (A , B) .sound ()
  ex .CBPVModel.O .F-hom (f , g) .carmap = {!   !}
  ex .CBPVModel.O .F-hom (f , g) .pres op args = {!   !}
  ex .CBPVModel.O .F-id =  {!   !}
  ex .CBPVModel.O .F-seq f g = {!   !}
-}
{-}
  ex : CBPVModel boopTheory 
  ex .CBPVModel.V = SET _
  ex .CBPVModel.C = WRITERALG _
  ex .CBPVModel.O .F-ob (A , B) .alg .Carrier = ⟨ A ⟩ → B .fst .fst
  ex .CBPVModel.O .F-ob (A , B) .alg .interp tt arg = arg zero
  ex .CBPVModel.O .F-ob (A , B) .sound ()
  ex .CBPVModel.O .F-hom (f , g) .carmap = λ z z₁ → g .fst (z (f z₁))
  ex .CBPVModel.O .F-hom (f , g) .pres op args = refl
  ex .CBPVModel.O .F-id = AlgHom≡ refl
  ex .CBPVModel.O .F-seq f g = AlgHom≡ refl
-}



  module Syntax (T : Theory) where 

    mutual 
      data VTy : Type where 
        Ans : VTy
        U : CTy → VTy

      data CTy : Type where 
        F : VTy → CTy


    data _⊢v_ : (A A' : VTy) → Type 
    data _⊢c_ : (A : VTy)(B : CTy) → Type 
    data _⊢k_ : (B B' : CTy) → Type 
    
    plug' : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B'
    ret' : {A : VTy} → A ⊢c F A
    data _⊢v_  where
      -- category 
      subV : ∀ {A A' A''} → A ⊢v A' → A' ⊢v A'' → A ⊢v A''
      var : ∀ {A} → A ⊢v A
      subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
      subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
      subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
        subV (subV V W) Y ≡ subV V (subV W Y)
      isSet⊢v : ∀{A A'} → isSet (A ⊢v A')

      tru : Ans ⊢v Ans 
      fls : Ans ⊢v Ans 

      -- types
      thunk : {A : VTy}{B : CTy} → (M : A ⊢c B) → A ⊢v U B

    data _⊢k_ where
      -- category 
      kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
      hole : ∀ {B} → B ⊢k B
      kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
      kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
      kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
        kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)
      isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

      bind : ∀{A B} → A ⊢c B → F A ⊢k B
      Fη : ∀ {A B}{S : F A ⊢k B} → S ≡ bind (plug' S ret')  


    ops' : ∀(A : VTy)(B : CTy)(op : T .Sig .Op) →  
        (Fin (T .Sig .arity op) → A ⊢c B) → A ⊢c B


    evalT : {A : VTy}{B : CTy}{n : ℕ}→ Term (T .Sig) n → (Fin n → A ⊢c B) → A ⊢c B
    evalT {A}{B} tm args = eval (record { Carrier = A ⊢c B , {!   !} ; interp = ops' A B }) tm args

    {-# NO_POSITIVITY_CHECK #-}
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
      ops : ∀(A : VTy)(B : CTy)(op : T .Sig .Op) →  
        (Fin (T .Sig .arity op) → A ⊢c B) → A ⊢c B
      eqs : ∀(A : VTy)(B : CTy)(eq : T .Eq)(args : Fin (T .ax eq .ctx) → A ⊢c B) 
        → evalT (T .ax eq .lhs) args ≡ evalT (T .ax eq .rhs) args 
      -- interaction with subC and plug
      opsSub : ∀{A A' : VTy}{B : CTy}(V : A ⊢v A')(op : T .Sig .Op) →  
        (args : Fin (T .Sig .arity op) → A' ⊢c B) → 
        subC V (ops A' B op args) ≡ ops A B op (λ x → subC V (args x))
      opsPlug :  ∀{A : VTy}{B B' : CTy}(S : B ⊢k B')(op : T .Sig .Op) →  
        (args : Fin (T .Sig .arity op) → A ⊢c B) → 
        plug S (ops  A B op args) ≡ ops A B' op (λ x → plug S (args x))

      -- connectives
      ret : {A : VTy} → A ⊢c F A
      -- adding this equations breaks agdas ability to match on A ⊢c B
      -- Fβ : ∀{A B M} → plug (bind M) ret ≡ M
      force : {B : CTy} → U B ⊢c B

    plug' = plug
    ret' = ret 
    ops' = ops


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


    FreeCompModel : VTy → CTy → Model T 
    FreeCompModel A B .alg .Carrier = A ⊢c B , isSet⊢c
    FreeCompModel A B .alg .interp = ops A B
    FreeCompModel A B .sound = eqs A B


  {-}
    FreeMor : {A : VTy}{B : CTy}(M : Model T) → 
      (f : A ⊢c B  → ⟨ M .alg .Carrier ⟩) → 
      (ModelCat T)[ FreeCompModel A B , M ]
    FreeMor M f .carmap N = {! N  !}
    FreeMor {A} {B} M f .pres = {!   !}
-}


    O : Functor (V ^op ×C C) (ModelCat T) 
    O .F-ob (A , B) = FreeCompModel A B
    O .F-hom (V , S) .carmap M = plug S (subC V M)
    O .F-hom (V , S) .pres op args = cong (λ h →  plug S h) (opsSub V op args) ∙ opsPlug S op λ x → subC V (args x)
    O .F-id = AlgHom≡ (funExt λ M → plugId ∙ subCId)
    O .F-seq (V , S)(V' , S') = AlgHom≡ (funExt λ M → sym plugDist ∙ cong₂ plug refl (sym plugSub ∙ sym subDist ∙ cong₂ subC refl plugSub))



    SyntaxModel : CBPVModel T
    SyntaxModel .CBPVModel.V = V
    SyntaxModel .CBPVModel.C = C
    SyntaxModel .CBPVModel.O = O

  module TypeStructure (T : Theory)(M : CBPVModel T) where 
    open CBPVModel M


    open import HyperDoc.Lib
    open import Cubical.Categories.Presheaf.Morphism.Alt
    open PshIso
    
    HasUTy : Type _
    HasUTy = (B : ob C) → Representation V (UF {T} ∘F O[-, B ])

    HasFTy : Type _
    HasFTy = (A : ob V) → Representation (C ^op) (UF {T} ∘F O[ A ,-] ∘F from^op^op)
{-}

{-}    to : {A : VTy}{B : CTy} → ModelCat T [ FreeCompModel A B  , FT .F-ob ((F A ⊢k B) , isSet⊢k) ]
    to {A} {B} .carmap M = inc (bind M)
    to {A} {B} .pres op args = {!  !}
      -- goal : inc (bind (ops A B op args)) ≡ ops op (λ x → inc (bind (args x)))
      -- bind (boop M) = 〚 boop 〛 (bind M)

    fro : {A : VTy}{B : CTy} → ModelCat T [ FT .F-ob ((F A ⊢k B) , isSet⊢k) , FreeCompModel A B ]
    fro {A}{B} = FreeModelMorphism {T}{F A ⊢k B}{FreeCompModel A B } λ S → plug S ret

-}
    hasUTy : HasUTy 
    hasUTy B .fst = U B
    hasUTy B .snd .trans .PshHom.N-ob A V = subC V force
    hasUTy B .snd .trans .PshHom.N-hom A A' V V' = {!   !}
    hasUTy B .snd .nIso A .fst = thunk
    hasUTy B .snd .nIso A .snd .fst _ = {!   !}
    hasUTy B .snd .nIso A .snd .snd _ = {!   !}
    
    -- type structure..
    FType : {A : VTy}{B : CTy} → 
      CatIso (ModelCat T) (FreeCompModel A B) (FT {T} .F-ob (F A ⊢k B , isSet⊢k)) 
    FType {A} {B} .fst = to {A}{B}
    FType {A} {B} .snd .isIso.inv = fro {A}{B}
    FType {A} {B} .snd .isIso.sec = 
      FreeModelMorphism! {T}{F A ⊢k B}{FT .F-ob ((F A ⊢k B) , isSet⊢k)} λ S → cong inc Fη
    FType {A} {B} .snd .isIso.ret = {!   !} -- AlgHom≡ (funExt λ M → Fβ)



    to' : {A : VTy}{B : CTy} → ModelCat T [ FreeModel T ⟨ (A ⊢v U B) , isSet⊢v ⟩ , FreeCompModel A B ] 
    to' {A}{B} = 
      FreeModelMorphism {T}{A ⊢v U B}{FreeCompModel A B } λ V → subC V force

    fro' : {A : VTy}{B : CTy} → ModelCat T [ FreeCompModel A B , FreeModel T ⟨ (A ⊢v U B) , isSet⊢v ⟩ ]
    fro' {A} {B} .carmap M = inc (thunk M)
    fro' {A} {B} .pres op args = {!   !}

    UType : {A : VTy}{B : CTy} → 
      CatIso (ModelCat T) ((FT {T} .F-ob (A ⊢v U B , isSet⊢v))) ((FreeCompModel A B)) 
    UType {A} {B} .fst = to' {A}{B}
    UType {A} {B} .snd .isIso.inv = fro' {A}{B}
    UType {A} {B} .snd .isIso.sec = AlgHom≡ {!   !}
    UType {A} {B} .snd .isIso.ret = {!   !}
-}

    {-}
    FType {A} {B} .fst .carmap M = inc (bind M)
    FType {A} {B} .fst .pres op args = {!   !}
    FType {A} {B} .snd .isIso.inv = 
      FreeModelMorphism {T}{F A ⊢k B}{O .F-ob (A , B)} λ S → plug S ret
    FType {A} {B} .snd .isIso.sec = {!   !}
    FType {A} {B} .snd .isIso.ret = AlgHom≡ (funExt λ M → Fβ{A}{B}{M})
    -}
    {-}
    FType : {A : VTy}{B : CTy} → 
      CatIso (ModelCat T) (O .F-ob (A , B)) (FT {T} .F-ob (F A ⊢k B , isSet⊢k)) 
    FType .fst .carmap M = inc (bind M)
    FType .fst .pres op args = {!   !}
    FType {A}{B} .snd .isIso.inv = FreeModelMorphism {T}{M = O .F-ob (A , B)} λ S → plug S ret
    FType .snd .isIso.sec = useful λ S → {!   !}
    FType .snd .isIso.ret = AlgHom≡ (funExt λ M → Fβ)
­-}


  module recursor 
    (N : CBPVModel boopTheory)
    (denAns : ob (CBPVModel.V N)) where
    -- (hasFTy : HasFTy N) where 

    open Syntax boopTheory
    open TypeStructure boopTheory
    module _ (hasFTy : HasFTy N) where 

      module N = CBPVModel N
        
      module T = Theory boopTheory
      module S = Signature (T.Sig)

      boop' : {A : VTy}{B : CTy} → (M : A ⊢c B) → A ⊢c B 
      boop' {A}{B} M = ops A B  tt λ _ → M
      
      -- example
      ex1 : {A : VTy}{B B' : CTy}{S : B ⊢k B'}{M : A ⊢c B} → 
        plug S (boop' M) ≡ boop' (plug S M) 
      ex1 {A}{B}{B'}{S}{M} = opsPlug S tt (λ _ → M)

      ex3 : {A : VTy}{B : CTy}{M : A ⊢c B} →
        (Fβ : ∀{A B M} → plug (bind M) ret ≡ M) → 
        boop' M ≡ plug (bind M) (boop' ret)
      ex3 Fβ = cong boop' (sym Fβ) ∙ sym ex1
      
      -- Fη : ∀ {A B}{S : F A ⊢k B} → S ≡ bind (plug' S ret')  
      ex2 : {A : VTy}{B : CTy}{M : A ⊢c B} →
        (Fβ : ∀{A B M} → plug (bind M) ret ≡ M) → 
        bind (boop' M)  ≡ kcomp (bind (boop' ret)) (bind M)
      ex2 {A}{B}{M} Fβ = cong bind (ex3 Fβ ∙ cong₂ plug refl (sym  Fβ) ∙ plugDist) ∙ sym Fη
        -- cong bind (ex3 Fβ) ∙ {!   !}
        -- cong bind {! ex2 Fβ !} ∙ {!   !}
        -- cong bind (cong boop' (sym Fβ)) ∙ cong bind (sym ex1) ∙ {!   !} 

      vty : V .ob → N.V .ob 
      vty A = {!   !}

      cty : C .ob → N.C .ob 
      cty B = {!   !}

      vtm : {A A' : V .ob} → A ⊢v A' → N.V [ vty A , vty A' ]
      vtm (subV V V') = N.V ._⋆_ (vtm V) (vtm V')
      vtm var = N.V .id
      vtm (subVIdl V i) = {!   !}
      vtm (subVIdr V i) = {!   !}
      vtm (subVAssoc V₁ V₂ V₃ i) = {!   !}
      vtm (isSet⊢v V₁ V₂ x y i i₁) = {!   !}
      vtm tru = {!   !}
      vtm fls = {!   !}
      vtm (thunk M) = {!   !} 
      
      ktm : {B B' : C .ob} → B ⊢k B' → N.C [ cty B , cty B' ]
      ktm (kcomp S S') = N.C ._⋆_ (ktm S) (ktm S')
      ktm hole = N.C .id
      ktm (kcompIdl S i) = {!   !}
      ktm (kcompIdr S i) = {!   !}
      ktm (kcompAssoc S S₁ S₂ i) = {!   !}
      ktm (isSet⊢k S S₁ x y i i₁) = {!   !}
      ktm (bind x) = {!   !}
      ktm (Fη i) = {!   !} 

      ctm : {A : V .ob}{B : C .ob} → A ⊢c B → N.O'[ vty A , cty B ]
      ctm (subC V M) = N.lcomp (vtm V) .carmap (ctm M)
      ctm (plug S M) = N.rcomp (ktm S) .carmap (ctm M)
      ctm (plugId i) = {!   !}
      ctm (subCId i) = {!   !}
      ctm (plugDist i) = {!   !}
      ctm (subDist i) = {!   !}
      ctm (plugSub i) = {!   !}
      ctm (isSet⊢c M M₁ x y i i₁) = {!   !}
      -- boop(M) := 〚 boop 〛 (〚 M 〛)
      ctm (ops A B tt x) = N.O[ vty A , cty B ] .alg .interp tt (λ a → ctm (x a))
      ctm (opsSub V₁ op args i) = {!   !}
      ctm (opsPlug S op args i) = {!   !}
      ctm ret = {!   !}
      ctm force = {!   !} 


      FV : Functor V N.V 
      FV .F-ob = vty
      FV .F-hom = vtm
      FV .F-id = refl
      FV .F-seq _ _ = refl

      FC : Functor C N.C 
      FC .F-ob = cty
      FC .F-hom = ktm
      FC .F-id = refl
      FC .F-seq _ _ = refl

      FO : NatTrans O (N.O ∘F ((FV ^opF)  ×F  FC)) 
      FO .N-ob (A , B) .carmap = ctm {A}{B}
      FO .N-ob (A , B) .pres tt arg = refl
      FO .N-hom (V , S) = AlgHom≡ (funExt λ M → {!   !}) -- just works

{-}
  module recursor 
    (T : Theory)
    (N : CBPVModel T)
    (denAns : ob (CBPVModel.V N)) where
    -- (hasFTy : HasFTy N) where 

    open Syntax T
    open TypeStructure T
    module _ (hasFTy : HasFTy N) where 

      module N = CBPVModel N
        
      module T = Theory T 
      module S = Signature (T.Sig)
      

      vty : V .ob → N.V .ob 
      vty = {!   !}

      cty : C .ob → N.C .ob 
      cty = {!   !}

      vtm : {A A' : V .ob} → A ⊢v A' → N.V [ vty A , vty A' ]
      vtm = {!   !} 
      
      ktm : {B B' : C .ob} → B ⊢k B' → N.C [ cty B , cty B' ]
      ktm = {!   !} 

      ctm : {A : V .ob}{B : C .ob} → A ⊢c B → N.O'[ vty A , cty B ]
      ctm = {!   !} 

      ctmHom : {A : V .ob}{B : C .ob} → 
        (op : S.Op)(args : Fin (S.arity op) → A ⊢c B) → 
        ctm (interp (FreeCompModel A B  .alg) op args) 
          ≡ 
        interp  (N.O[ vty A , cty B ] .alg) op (λ a → ctm (args a))
      ctmHom {A}{B} op args = {! N.O'[ vty A , cty B ] !}

      FV : Functor V N.V 
      FV .F-ob = vty
      FV .F-hom = vtm
      FV .F-id = {!   !}
      FV .F-seq = {!   !}

      FC : Functor C N.C 
      FC .F-ob = cty
      FC .F-hom = ktm
      FC .F-id = {!   !}
      FC .F-seq = {!   !}

      FO : NatTrans O (N.O ∘F ((FV ^opF)  ×F  FC)) 
      FO .N-ob (A , B) .carmap = ctm
      FO .N-ob (A , B) .pres = {!   !}
        -- ctmHom {A}{B}
      FO .N-hom = {!   !}

-}

-- examples

  data Ops : Type where 
    e ● : Ops

  data Eqs : Type where 
    lunit runit assoc : Eqs
  
  monoidSig : Signature
  monoidSig .Op = Ops
  monoidSig .arity e = 0
  monoidSig .arity ● = 2

  monoidThy : Theory 
  monoidThy .Theory.Sig = monoidSig
  monoidThy .Theory.Eq = Eqs
  monoidThy .Theory.ax lunit = record { ctx = 1 ; lhs = var zero ; rhs = app ● λ{ zero → var zero
                                                                                ; (suc d) → app e λ()} }
  monoidThy .Theory.ax runit = record { ctx = 1 ; lhs = var zero ; rhs = app ● λ { zero → app e λ()
                                                                                 ; (suc d) → var zero } }
  monoidThy .Theory.ax assoc .Equation.ctx = 3
  monoidThy .Theory.ax assoc .Equation.lhs = app ● λ {zero → var zero
                                                    ; one → app ● λ { zero → var one
                                                                    ; one → var two}}
  monoidThy .Theory.ax assoc .Equation.rhs = app ● λ {zero → app ● λ { zero → var zero
                                                                    ; one → var one}
                                                    ; one → var two}


  monoidAlg : Alg monoidSig
  monoidAlg .Carrier = List Unit , {!   !}
  monoidAlg .interp e  _ = []
  monoidAlg .interp ● args = args zero ++ args one

  monoidModel : Model monoidThy
  monoidModel .Model.alg = monoidAlg
  monoidModel .Model.sound lunit args = sym (++-unit-r  _)
  monoidModel .Model.sound runit args = refl
  monoidModel .Model.sound assoc args = sym (++-assoc (args zero) (args one) (args two))

  -}