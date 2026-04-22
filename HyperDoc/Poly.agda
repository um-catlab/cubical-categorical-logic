{-# OPTIONS --type-in-type #-}

-- for Generalized polynomials
module HyperDoc.Poly where 

open import Cubical.Data.Nat
open import Cubical.Data.Unit 
open import Cubical.Data.Sum renaming (map to ⊎map ; rec to ⊎rec)
open import Cubical.Data.FinData hiding (snotz)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure hiding(str)

-- open import Cubical.Categories.Presheaf.Properties 
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf hiding (PshIso ; Representation)
--open import Cubical.Categories.Instances.Presheaf
open import HyperDoc.Lib 
open import Cubical.Categories.NaturalTransformation
open NatTrans
open PshHom

open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Yoneda 
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Instances.Functors
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Bifunctor
--open import Cubical.Categories.Presheaf.CCC 
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base
-- open import HyperDoc.FinDataUP
open Category
open Functor
open FinSumChar renaming (inv to match)

open Iso
open import Cubical.Categories.Limits.Cartesian.Base
module hoas (CC : CartesianCategory _ _ )where 

  open CartesianCategory CC renaming (_×_ to _×bp_)
  PshC : Category _ _ 
  PshC = PresheafCategory C _
  -- open BinProductsNotation bp renaming (_×_ to _×bp_)

  _ext_ : (A : ob PshC)(X : ob C) → ob PshC 
  (A ext X) .F-ob Y = A .F-ob (X ×bp Y)
  (A ext X) .F-hom {Y}{Z} f = A .F-hom (C .id ×p f)
  (A ext X) .F-id = cong (λ h → A .F-hom h) {! ×Bif .  !} ∙ A .F-id
  (A ext X) .F-seq = {!   !}

  -- this is not the usual exponential of presheaves ?
  _⇒Psh_ : ob PshC → ob PshC → ob PshC 
  (A ⇒Psh B) .F-ob X = PshC [ A , B ext X ] , isSetHom PshC
  (A ⇒Psh B) .F-hom {X} {Y} f n .N-ob Z Az = B .F-hom (f ×p C .id) (n .N-ob Z Az)
  (A ⇒Psh B) .F-hom {X} {Y} f n .N-hom {Z}{W} g = funExt λ Az → {!   !}
  (A ⇒Psh B) .F-id = {!   !}
  (A ⇒Psh B) .F-seq = {!   !}

  --app : {A B : ob PshC} → PshC [ (A ⇒Psh B) ×Psh A , B ] 
 --- app {A} {B} .N-ob X (n , Ax) = B .F-hom {!   !} (n .N-ob X Ax)
  --app {A} {B} .N-hom = {!   !}

  --open import Cubical.Data.Nat
  open import Cubical.Data.Sigma

  open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥rec∥; map to ∥map∥)
  -- https://github.com/niccoloveltri/final-pfin/blob/main/Pfin/AsFreeJoinSemilattice.agda
  data Pfin {ℓ} (A : Type ℓ) : Type ℓ where
    ø     : Pfin A
    η     : A → Pfin A
    _∪_   : Pfin A → Pfin A → Pfin A
    com  : ∀ x y → x ∪ y ≡ y ∪ x
    ass : ∀ x y z → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
    idem  : ∀ x → x ∪ x ≡ x
    nr  : ∀ x → x ∪ ø ≡ x
    trunc : isSet (Pfin A)

  open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ ; inl to inlₚ ; inr to inrₚ) 

  -- not possible to eliminate into hSet..(⊎ not idempotent)
  _∈ₛ_ : ∀{A : Type} → A → Pfin A → hProp _
  x ∈ₛ ø = ⊥ₚ
  x ∈ₛ η y = x ≡ₚ y
  x ∈ₛ (s₁ ∪ s₂) = (x ∈ₛ s₁) ⊔ (x ∈ₛ s₂)
  x ∈ₛ com s₁ s₂ i =
    ⇔toPath {_} {x ∈ₛ s₁ ⊔ x ∈ₛ s₂} {x ∈ₛ s₂ ⊔ x ∈ₛ s₁}
      (∥map∥ λ { (inl m) → inr m ; (inr m) → inl m})
      (∥map∥ λ { (inl m) → inr m ; (inr m) → inl m})
      i
  x ∈ₛ ass s₁ s₂ s₃ i = 
    ⇔toPath {_} {x ∈ₛ s₁ ⊔ x ∈ₛ s₂ ⊔ x ∈ₛ s₃} {(x ∈ₛ s₁ ⊔ x ∈ₛ s₂) ⊔ x ∈ₛ s₃} {!   !} {!   !} 
      {-(∥rec∥ ? λ { (inl m) → inl (inl m)
                              ; (inr m) → ∥map∥ (⊎map inr (λ y → y)) m})
      (∥rec∥ ? λ { (inl m) → ∥map∥ (⊎map(λ y → y) inl) m
                              ; (inr m) → inr (inr m)}) -}
      i
  x ∈ₛ idem s i =
    ⇔toPath {_} {x ∈ₛ s ⊔ x ∈ₛ s} {x ∈ₛ s}
      (∥rec∥ (isProp⟨⟩ (x ∈ₛ s)) (λ { (inl m) → m ; (inr m) → m }))
      ((λ x → ∣ inl x ∣₁)) 
      i
  x ∈ₛ nr s i = 
    ⇔toPath {_} {x ∈ₛ s ⊔ ⊥ₚ} {x ∈ₛ s}
    (∥rec∥ (isProp⟨⟩ (x ∈ₛ s)) (λ { (inl m) → m ; (inr ()) }))
    (λ x → ∣ inl x ∣₁) 
    i
  x ∈ₛ trunc s₁ s₂ p q i j =
    isSetHProp (x ∈ₛ s₁) (x ∈ₛ s₂) (cong (x ∈ₛ_) p) (cong (x ∈ₛ_) q) i j
  

  module _ {ℓ}{A B : Type ℓ} (Bset : isSet B)
          (bø : B) (bη : A → B)
          (_b∪_ : B → B → B)
          (bcom  : ∀ x y → x b∪ y ≡ y b∪ x)
          (bass : ∀ x y z → x b∪ (y b∪ z) ≡ (x b∪ y) b∪ z)
          (bidem  : ∀ x → x b∪ x ≡ x)
          (bnr  : ∀ x → x b∪ bø ≡ x) where

    recPfin : Pfin A → B
    recPfin ø = bø
    recPfin (η x) = bη x
    recPfin (s ∪ s₁) = (recPfin s) b∪ (recPfin s₁)
    recPfin (com s s₁ i) = bcom (recPfin s) (recPfin s₁) i
    recPfin (ass s s₁ s₂ i) = bass (recPfin s) (recPfin s₁) (recPfin s₂) i
    recPfin (idem s i) = bidem (recPfin s) i
    recPfin (nr s i) = bnr (recPfin s) i
    recPfin (trunc s s₁ x y i i₁) =
      Bset (recPfin s) (recPfin s₁)
          (\ j → recPfin (x j)) (\ j → recPfin (y j))
          i i₁

  open import Cubical.Data.Empty 

  _∈_ :  {X : Type} → X → Pfin X → Type
  _∈_ x Γ = ⟨ x ∈ₛ Γ ⟩

  _∉_ :  {X : Type} → X → Pfin X → Type
  _∉_ x Γ = x ∈ Γ → ⊥


  fresh' : Pfin ℕ → ℕ 
  fresh' X = 1 + 
    (recPfin 
      isSetℕ 
      0 
      (max 0) 
      max 
      maxComm 
      {!   !} -- yes, (x y z : ℕ) → max x (max y z) ≡ max (max x y) z
      {!   !} -- yes, (x : ℕ) → max x x ≡ x
      (λ { zero → refl
         ; (suc n) → refl})
      X) 

  _ : fresh' (η 5 ∪ η 7)  ≡ 8
  _ = refl

  lem : {Γ Δ : Pfin ℕ}{n : ℕ} → n ∉ (Γ ∪ Δ) → n ∉ Γ 
  lem = {!   !}

  lem' : {Γ Δ : Pfin ℕ}{n : ℕ} → n ∉ (Δ ∪ Γ) → n ∉ Γ 
  lem' {Γ}{Δ}{n} prf = lem (subst (λ h → n ∉ h) (com _ _) prf)


  isFresh' : (Γ : Pfin ℕ) → fresh' Γ ∉ Γ  in Var
  isFresh' (η zero) prf = ∥rec∥ (λ()) snotz prf
  isFresh' (η (suc x)) prf =  ∥rec∥ (λ()) sucn≠n prf
  isFresh' (Γ ∪ Γ') prf = ∥rec∥ (λ()) {!   !} prf -- recursive call is not strictly smaller
   --  ∥rec∥ (λ()) (⊎rec (lem (isFresh' (Γ ∪ Γ'))) (lem' (isFresh' (Γ ∪ Γ')))) prf
  isFresh' (com Γ Γ₁ i) prf = {!   !}
  isFresh' (ass Γ Γ₁ Γ₂ i) prf = {!   !}
  isFresh' (idem Γ i) prf = {!   !}
  isFresh' (nr Γ i) prf = {!   !}
  isFresh' (trunc Γ Γ₁ x y i i₁) prf = {!   !}

  module _ 
      (Var : Type)
      (fresh : Pfin Var → Var)  
      (isFresh : (Γ : Pfin Var) → fresh Γ ∉ Γ)
      where

 --   open import Cubical.Foundations.Powerset
    open import Cubical.Categories.Displayed.Constructions.HomPropertyOver
    open import Cubical.Categories.Constructions.TotalCategory


    data Tm (V : Pfin Var) : Type where 
      var : (v : Var) → v ∈ V → Tm V 
      app : Tm V → Tm V → Tm V
      lam : (Var → Tm V) → Tm V

    varSub : Pfin Var → Pfin Var → Type
    varSub X Y = (v : Var) → v ∈ Y → Σ Var λ v' → v' ∈ X

    Rename : Category _ _ 
    Rename .ob = Pfin Var
    Rename .Hom[_,_] = varSub
    Rename .id {X} v v∈X = v , v∈X
    Rename ._⋆_ {X}{Y}{Z} δ γ v v∈Z = δ (γ v v∈Z .fst) (γ v v∈Z .snd)
    Rename .⋆IdL _ = refl
    Rename .⋆IdR _ = refl
    Rename .⋆Assoc _ _ _ = refl
    Rename .isSetHom = {!   !}

    tmSub : Pfin Var → Pfin Var → Type 
    tmSub Δ Γ = (x : Var) → x ∈ Γ → Tm Δ

    substitution : {Γ Δ : Pfin Var} → tmSub Δ Γ → Tm Γ → Tm Δ 
    substitution {Γ} {Δ} γ (var v x) = γ v x
    substitution {Γ} {Δ} γ (app t t') = app (substitution γ t) (substitution γ t')
    substitution {Γ} {Δ} γ (lam f) = lam λ x → substitution γ (f x)
    
    subId : {Γ : Pfin Var}{t : Tm Γ} → substitution {Γ}{Γ} var t ≡ t 
    subId {Γ} {var v x} = refl
    subId {Γ} {app t t₁} = cong₂ app subId subId
    subId {Γ} {lam x} = cong lam (funExt λ y → subId) 
    
    SubstCat : Category _ _ 
    SubstCat .ob = Pfin Var
    SubstCat .Hom[_,_] = tmSub
    SubstCat .id {Γ} x x∈Γ = var x x∈Γ
    SubstCat ._⋆_ {Θ}{Δ}{Γ} δ γ x x∈Γ = substitution δ (γ x x∈Γ)
    SubstCat .⋆IdL {Δ}{Γ} γ = funExt λ x → funExt λ x∈Γ → subId 
    SubstCat .⋆IdR {Δ}{Γ} γ = refl
    SubstCat .⋆Assoc = {!   !}
    SubstCat .isSetHom = {!   !}


    --_⨄_ : Pfin Var → Pfin Var → Pfin Var 
    --_⨄_ Γ Δ = {!   !}



    Ren' : HomPropertyOver SubstCat _
    HomPropertyOver.Hom[ Ren' ][-,-] {Δ}{Γ} γ = (x : Var)(x∈Γ : x ∈ Γ) → Σ[ y ∈ Var ] Σ[ y∈Δ ∈ (y ∈ Δ) ] γ x x∈Γ ≡ var y y∈Δ
    Ren' .HomPropertyOver.isPropHomᴰ = {!   !}
    Ren' .HomPropertyOver.idᴰ {Γ} x x∈Γ = x , (x∈Γ , refl)
    Ren' .HomPropertyOver._⋆ᴰ_ {Θ}{Δ}{Γ} γ δ isvar isvar' x x∈Γ = {!  !} , ({!   !} , {!   !})

    Ren : Category _ _ 
    Ren = ∫C (HomPropertyOver→Catᴰ Ren')

    PshVar : Category _ _ 
    PshVar = PresheafCategory Ren _

    pVar : ob PshVar 
    pVar .F-ob (Γ , _) = (Σ[ x ∈ Var ] (x ∈ Γ)) , {!   !}
    pVar .F-hom = λ z z₁ →
        z .snd (z₁ .fst) (z₁ .snd) .fst ,
        z .snd (z₁ .fst) (z₁ .snd) .snd .fst
    pVar .F-id = refl
    pVar .F-seq _ _ = refl

    pTm : ob PshVar 
    pTm .F-ob (Γ , _) = (Tm Γ) , {!   !}
    pTm .F-hom (γ , _) t = substitution γ t
    pTm .F-id = funExt λ _ → subId
    pTm .F-seq γ δ = funExt λ t → {!   !}

    papp : PshVar [ pTm ×Psh pTm , pTm ] 
    papp .N-ob (Γ , _) (t , t') = app t t'
    papp .N-hom _ = refl

    plam : PshVar [ {!   !} , pTm ] 
    plam = {!   !}

    ext : Pfin Var → Pfin Var
    ext Γ = Γ ∪ η (fresh Γ)
    
    -- can't define, isProp (Tm (ext (Δ .fst)))
    extMap : {Γ Δ : ob Ren} → Ren [ Δ , Γ ] → Ren [ (ext (Δ .fst) , tt) , (ext (Γ .fst) , tt) ]
    extMap γ .fst x = {!   !}
      --  ∥rec∥  {!   !} (⊎rec (λ x∈Γ → {!   !}) λ xfresh → {! var  !})
    extMap γ .snd = {!   !}

    pext : ob PshVar → ob PshVar  
    pext A .F-ob (Γ , _ ) = A .F-ob (ext Γ , tt)
    pext A .F-hom {Γ}{Δ} γ = A .F-hom (extMap γ)
    pext A .F-id = {!   !}
    pext A .F-seq = {!   !}




    {-
  _ext_ : (A : ob PshC)(X : ob C) → ob PshC 
  (A ext X) .F-ob Y = A .F-ob (X ×bp Y)
  (A ext X) .F-hom {Y}{Z} f = A .F-hom (C .id ×p f)
  (A ext X) .F-id = cong (λ h → A .F-hom h) {! ×Bif .  !} ∙ A .F-id
  (A ext X) .F-seq = {!   !}

  -- this is not the usual exponential of presheaves ?
  _⇒Psh_ : ob PshC → ob PshC → ob PshC 
  (A ⇒Psh B) .F-ob X = PshC [ A , B ext X ] , isSetHom PshC
  (A ⇒Psh B) .F-hom {X} {Y} f n .N-ob Z Az = B .F-hom (f ×p C .id) (n .N-ob Z Az)
  (A ⇒Psh B) .F-hom {X} {Y} f n .N-hom {Z}{W} g = funExt λ Az → {!   !}
  (A ⇒Psh B) .F-id = {!   !}
  (A ⇒Psh B) .F-seq = {!   !}
    -}

{-
    substitution : Pfin Var → Pfin Var → Type
    substitution X Y = (y : Var) → y ∈ Y → Tm X
    
    SubCat : Category _ _ 
    SubCat .ob = Pfin Var
    SubCat .Hom[_,_] = substitution
    SubCat .id {X} v v∈X = var v v∈X
    SubCat ._⋆_ {X}{Y}{Z} δ γ v v∈Z = δ v {! γ v  !}
    SubCat .⋆IdL = {!   !}
    SubCat .⋆IdR = {!   !}
    SubCat .⋆Assoc = {!   !}
    SubCat .isSetHom = {!   !}
-}
  -- if Var := Nat 
  -- adequacy is lost (we've broken into the meta lanuage since we can define a function Var → Tm Var via pattern matching on ℕ)
  -- solution in Higher-order abstract syntax in Coq
  -- well define well formed terms where Var := Nat 




record FinPoly (ℓ : Level) : Type (ℓ-suc ℓ) where 
  constructor _◂_ 
  field 
    pos : ℕ 
    dir : Fin pos → hSet ℓ


⦅_⦆' : {ℓ  : Level} → FinPoly ℓ  → Type ℓ → Type ℓ 
⦅ pos ◂ dir ⦆' X  = Σ[ x ∈ Fin pos ] (⟨ dir x ⟩ → X )

⦅_⦆ : {ℓ  : Level} → FinPoly ℓ  → hSet ℓ → hSet ℓ 
⦅ pos ◂ dir ⦆ X .fst = Σ[ x ∈ Fin pos ] (⟨ dir x ⟩ → ⟨ X ⟩)
⦅ pos ◂ dir ⦆ X .snd = {!   !}
  -- Σ[ p ∈ ⟨ pos ⟩  ] ((⟨ dir p ⟩ → ⟨ X ⟩ ))) , isSetΣ (pos .snd) λ _ → isSet→ (X .snd)

data μ (p : FinPoly _) : Type where 
  inF : ⦅ p ⦆' (μ p) → μ p

data FreeOn (p : FinPoly _ )(X : Type) : Type where 
  var : X → FreeOn p X
  inF : ⦅ p ⦆' (FreeOn p X) → FreeOn p X

-- https://github.com/um-catlab/cbpv-functorial-opsem/blob/main/agda/code-samples/gsos.agda
  
-- Y ↦ Σ(i ∈ I) SET[ Xᵢ , Y ]
den : {ℓ  : Level} → FinPoly ℓ → Functor (SET ℓ) (SET ℓ) 
den P .F-ob X = ⦅ P ⦆ X
den P .F-hom f (n , d) = n , λ z → f (d z)
den P .F-id = refl
den P .F-seq _ _ = refl


open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Limits.Initial 
open import Cubical.Data.Sigma 
open Algebra
open AlgebraHom

module InitVar (p : FinPoly _)  where
  Sig = den p

  AlgΣ : Category _ _ 
  AlgΣ = AlgebrasCategory Sig

  IAlg : Type → ob AlgΣ 
  IAlg n .Algebra.carrier = (FreeOn p n) , {!   !}
  IAlg n .Algebra.str = inF



  {-# TERMINATING #-}
  Irec : {A : ob AlgΣ} → (X : Type)(γ : X → ⟨ A .carrier ⟩ ) → FreeOn p X → ⟨ A .carrier ⟩ 
  Irec {A} X γ (var x) = γ x
  Irec {A} X γ (inF x) = A .str (den p .F-hom (Irec {A} X γ) x)

  IHom : {A : ob AlgΣ} → (X : Type)(γ : X → ⟨ A .carrier ⟩ ) →  AlgΣ [ IAlg X , A ] 
  IHom {A} X γ .carrierHom = Irec {A} X γ
  IHom {A} X γ .strHom = refl

  Init :  (X : Type) → Initial AlgΣ 
  Init X .fst .carrier = FreeOn p X , {!   !}
  Init X .fst .str = inF
  Init X .snd A .fst = IHom {A} X {!   !}
  Init X .snd A .snd = {!   !}

module Init (p : FinPoly _)  where 
  Sig = den p

  AlgΣ : Category _ _ 
  AlgΣ = AlgebrasCategory Sig

  IAlg : ob AlgΣ 
  IAlg .Algebra.carrier = ((μ p)) , {!   !}
  IAlg .Algebra.str = inF

  {-# TERMINATING #-}
  Irec : {A : ob AlgΣ} → μ p → ⟨ A .carrier ⟩ 
  Irec {A} (inF x) = A .str (den p .F-hom (Irec {A}) x)

  IHom : {A : ob AlgΣ} →  AlgΣ [ IAlg , A ] 
  IHom {A} .carrierHom = Irec {A}
  IHom {A} .strHom = refl

  Init : Initial AlgΣ 
  Init .fst .Algebra.carrier = (μ p) , {!   !}
  Init .fst .Algebra.str = inF
  Init .snd A = IHom {A} , λ f → AlgebraHom≡ _ (funExt (goal f)) where 
    goal : (f : AlgΣ [ Init .fst , A ]) → (x : μ p) → Irec {A} x ≡ carrierHom f x
    goal f (inF x) = cong (λ  h → A .str h ) (ΣPathP (refl , funExt λ e → goal f (x .snd e))) ∙ sym (funExt⁻ (f .strHom) x) 


module example where 
  -- bialgebra
  st : FinPoly _  
  st .FinPoly.pos = 4
  st .FinPoly.dir zero = Fin 2 , isSetFin
  st .FinPoly.dir one = (Fin 1) , isSetFin
  st .FinPoly.dir two = (Fin 1) , isSetFin
  -- dead const
  st .FinPoly.dir three = (Fin 0) , isSetFin


  open Init st

  StΣ : Functor (SET _) (SET _) 
  StΣ = den st

  StAlg : Category _ _ 
  StAlg = AlgΣ

  sexp = ⟨ Init .fst .carrier ⟩


  get : sexp → sexp → sexp  
  get m n  = inF (zero , λ {zero → m
                          ; one → n })

  set0 : sexp → sexp 
  set0 m = inF (one , (λ _ → m))

  set1 : sexp → sexp 
  set1 m = inF (two , (λ _ → m))

  done : sexp 
  done = inF (three , (λ ()))

  e : sexp 
  e = get (set1 done) done






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

open FinProdChar

_⊗_ : FinPoly ℓ-zero → FinPoly ℓ-zero → FinPoly ℓ-zero
(n ◂ dir) ⊗ (m ◂ dir₁) = {! n * m  !} ◂ {!   !}
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
  LC = {!   !}

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