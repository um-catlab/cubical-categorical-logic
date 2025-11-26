{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.CBPV.Instances.DefinedSubstitution where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.List hiding (elim; [_])
open import Cubical.Data.List.Dependent

open import Cubical.Categories.WithFamilies.Simple.Instances.Free.Base
  renaming (ren to ren'; wkRen to wkRen' ; idRen to idRen' ; Var to Var' ; 
  Var' to none)


mutual 
  data CTy : Type where 
    fun : VTy → CTy → CTy 
    F : VTy → CTy 

  data VTy : Type where 
    one : VTy 
    prod : VTy → VTy → VTy 
    U : CTy → VTy


isSetVTy : isSet VTy 
isSetVTy = {!   !}

hGTy : hGroupoid _
hGTy = VTy , isOfHLevelSuc 2 isSetVTy

Var = Var' hGTy

Ctx = List ⟨ hGTy  ⟩ 

· : Ctx 
· = List.[]

_,,_ : VTy → Ctx → Ctx 
A ,, Γ = A List.∷ Γ

mutual 
  data _⊢v_  : Ctx → VTy →  Set where 
    var : {Γ : Ctx}{A : VTy} → 
      Var Γ A → 
      -------------------
      Γ ⊢v A 

    u : {Γ : Ctx} → 
      ----------
      Γ ⊢v one
    pair : {Γ : Ctx}{A A' : VTy} → 
      Γ ⊢v A → 
      Γ ⊢v A' → 
      -----------------
      Γ ⊢v (prod A A')
    thunk : {Γ : Ctx}{B : CTy} → 
      Γ ⊢c B → 
      ----------
      Γ ⊢v U B

  data _⊢c_ : Ctx → CTy → Set where 
    ret : {Γ : Ctx}{A : VTy} → 
      Γ ⊢v A → 
      --------- 
      Γ ⊢c F A

    force : {Γ : Ctx}{B : CTy} → 
      Γ ⊢v U B → 
      ----------- 
      Γ ⊢c B

    lam : {Γ : Ctx}{A : VTy}{B : CTy} →  
      (A ,, Γ) ⊢c B → 
      ---------------- 
      Γ ⊢c fun A B
    app : {Γ : Ctx}{A : VTy}{B : CTy} → 
      Γ ⊢c fun A B → 
      Γ ⊢v A → 
      ---------------- 
      Γ ⊢c B
    
    rec× : { Γ : Ctx} {A A' : VTy}{ B : CTy} → 
      Γ ⊢v (prod A A') → 
      (A ,, (A' ,, Γ)) ⊢c B → 
      -------------------- 
      Γ ⊢c B

    bind : {Γ : Ctx}{A : VTy}{B : CTy} → 
      Γ ⊢c F A → 
      (A ,, Γ) ⊢c B → 
      ----------- 
      Γ ⊢c B
        
  data _◂_⊢k_ : Ctx → CTy → CTy → Set where
    varc : {Γ : Ctx}{B : CTy} → Γ ◂ B ⊢k B
    ∙V : {Γ : Ctx}{A : VTy}{B B' : CTy} → 
      Γ ⊢v A → 
      Γ ◂ B ⊢k fun A B' → 
      -----------------------------
      Γ ◂ B ⊢k B'
    x←∙:M : {Γ : Ctx}{A : VTy}{B B' : CTy} →
      Γ ◂ B ⊢k F A → 
      (A ,, Γ) ⊢c B' → 
      -----------------------------------
      Γ ◂ B ⊢k B'

open import Cubical.Data.Unit
open import Cubical.Data.Sigma 
open import Cubical.Data.Sum renaming (rec to ⊎rec)


Sub[_,_] : Ctx → Ctx → Type 
Sub[_,_] Δ = ListP (Δ ⊢v_)

private
  variable
    A A' X Y : VTy
    B B' : CTy
    Δ Δ' Γ Θ Ξ ξ : Ctx
    γ  : Sub[ Δ , Γ ]

index : Sub[ Δ , Γ ] → (x : Var Γ A) → Δ ⊢v A 
index (y ∷ γ) vz = y
index (y ∷ γ) (vs x) = index γ x

Ren[_,_] = Renaming hGTy 
ren = ren' hGTy
wkRen = wkRen' hGTy
idRen = idRen' hGTy

liftRen : Ren[ Δ , Γ ] → Ren[ (A ,, Δ) , (A ,, Γ) ] 
liftRen γ = vz ∷ wkRen γ

mutual
  renSubv : Ren[ Δ , Γ ] → Γ ⊢v A → Δ ⊢v A 
  renSubv γ (var x) = var (ren γ x)
  renSubv γ u = u
  renSubv γ (pair v w) = pair (renSubv γ v) (renSubv γ w)
  renSubv γ (thunk m) = thunk (renSubc γ m)

  renSubc : Ren[ Δ , Γ ] → Γ ⊢c B → Δ ⊢c B 
  renSubc γ (ret x) = ret (renSubv γ x)
  renSubc γ (force v) = force (renSubv γ v)
  renSubc γ (lam m) = lam (renSubc (liftRen γ) m)
  renSubc γ (app m v) = app (renSubc γ m) (renSubv γ v)
  renSubc γ (rec× v m) = rec× (renSubv γ v) (renSubc (liftRen (liftRen γ)) m)
  renSubc γ (bind m n) = bind (renSubc γ m) (renSubc (liftRen γ) n)

wksub : Sub[ Δ , Γ ] → Sub[ A ,, Δ ,  Γ ]
wksub {Δ}{Γ}{A} γ = mapOverIdfun (λ A v → renSubv (wkRen  (idRen _)) v) _ γ

liftSub : Sub[ Δ , Γ ] → Sub[ A ,, Δ , A ,, Γ ]
liftSub {Δ}{Γ}{A} γ = var vz ∷ wksub γ

mutual 
  subv : Sub[ Δ , Γ ] → Γ ⊢v A → Δ ⊢v A 
  subv γ (var x) = index γ x
  subv γ u = u
  subv γ (pair v w) = pair (subv γ v) (subv γ w)
  subv γ (thunk m) = thunk (subc γ m)

  subc : Sub[ Δ , Γ ] → Γ ⊢c B → Δ ⊢c B
  subc γ (ret v) = ret (subv γ v)
  subc γ (force v) = force (subv γ v)
  subc γ (lam m) = lam (subc (liftSub γ) m)
  subc γ (app m v) = app (subc γ m) (subv γ v)
  subc γ (rec× v m) = rec× (subv γ v) (subc (liftSub(liftSub γ)) m)
  subc γ (bind m n) = bind (subc γ m) (subc (liftSub γ) n)

idSub : ∀ {Γ} → Sub[ Γ , Γ ]
idSub {[]} = []
idSub {x ∷ Γ} = (var vz) ∷ wksub idSub

_⋆Sub_ : Sub[ Θ , Δ ] → Sub[ Δ , Γ ] → Sub[ Θ , Γ ] 
δ ⋆Sub [] = []
δ ⋆Sub (x ∷ γ) = subv δ x ∷ (δ ⋆Sub γ)

subWkSub : ∀ (γ : Sub[ Δ , Γ ])(v : Var Γ A) → 
  subv (wksub {A = A}idSub) (var v) ≡ var (vs v) 
subWkSub γ vz = refl
subWkSub (y ∷ γ) (vs v) = {!   !}

s⟨_⟩∷⟨_⟩ :
  ∀ {x x' : Δ ⊢v A}{γ γ' : Sub[ Δ , Γ ]}
  → x ≡ x'
  → γ ≡ γ'
  → Path (Sub[ Δ , (A ∷ Γ)]) (x ∷ γ) (x' ∷ γ')
s⟨ x ⟩∷⟨ γ ⟩ i = x i ∷ γ i


indexId : (x : Var Γ A) → index idSub x ≡ var x
indexId vz = refl
indexId (vs x) = {!   !} 

mutual 
  subvId : (v : Γ ⊢v A) → subv idSub v ≡ v 
  subvId (var x) = {! refl  !}
  subvId u = refl
  subvId (pair v w) = cong₂ pair (subvId v) (subvId w)
  subvId (thunk m) = cong thunk (subcId m)

  subcId : (m : Γ ⊢c B) → subc idSub m ≡ m 
  subcId (ret v) = cong ret (subvId v)
  subcId (force v) = cong force (subvId v)
  subcId (lam m) = cong lam {!   !}
  subcId (app m v) = cong₂ app (subcId m) (subvId v)
  subcId (rec× v m) = cong₂ rec× (subvId v) {!   !}
  subcId (bind m n) = cong₂ bind (subcId m) {!   !}


subvAssoc : (f : Sub[ Δ , Γ ]) (g : Sub[ Θ , Δ ]) →
  subv (g ⋆Sub f) ≡ (λ x₁ → subv g (subv f x₁))
subvAssoc = {!   !}

⋆Sub⋆IdL : (γ : Sub[ Δ , Γ ]) → 
  (idSub ⋆Sub γ) ≡ γ 
⋆Sub⋆IdL [] = refl
⋆Sub⋆IdL (v ∷ γ) = s⟨ subvId v ⟩∷⟨ ⋆Sub⋆IdL γ ⟩

⋆Sub⋆IdR : {Γ : Ctx} → (γ : Sub[ Δ , Γ ]) → 
  (γ ⋆Sub idSub) ≡ γ 
⋆Sub⋆IdR {Γ} [] = {!   !}
⋆Sub⋆IdR {[]} (y ∷ γ) = {!   !}
⋆Sub⋆IdR {A ∷ Γ} (y ∷ γ) = {!   !}

⋆Sub⋆Assoc : ∀ (f : Sub[ ξ , Θ ]) (g : Sub[ Θ , Δ ]) (h : Sub[ Δ , Γ ]) →
  ((f ⋆Sub g) ⋆Sub h) ≡ (f ⋆Sub (g ⋆Sub h))
⋆Sub⋆Assoc _ _ [] = refl
⋆Sub⋆Assoc _ _ (y ∷ h) = s⟨ {! funExt (subvAssoc _ _)!} ⟩∷⟨ ⋆Sub⋆Assoc _ _ _ ⟩

open import Cubical.Foundations.Function

subv⋆ : ∀ {Γ Δ Θ : Ctx} → (g : Sub[ Θ , Δ ]) (f : Sub[ Δ , Γ ])(x : Γ ⊢v A) → 
  subv (g ⋆Sub f) x ≡ (subv g ((subv f) x))
subv⋆ g f x = {!   !}

open import Cubical.Categories.CBPV.Base
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open Functor
open Category
open CBPVModel
open import Cubical.Categories.Limits.Terminal.More

SubCat : Category _ _ 
SubCat .ob = Ctx
SubCat .Hom[_,_] = Sub[_,_]
SubCat .id = idSub
SubCat ._⋆_ = _⋆Sub_
SubCat .⋆IdL = ⋆Sub⋆IdL
SubCat .⋆IdR = ⋆Sub⋆IdR
SubCat .⋆Assoc = ⋆Sub⋆Assoc
SubCat .isSetHom = isOfHLevelSucSuc-ListP 0 λ _ → {!   !}

vTm : VTy → Functor (SubCat ^op) (SET _)
vTm A .F-ob Γ = (Γ ⊢v A) , {!   !}
vTm A .F-hom = subv
vTm A .F-id = funExt subvId
vTm A .F-seq f g = funExt (subv⋆ _ _)

ηterm : (Γ : Ctx)(γ : Sub[ Γ  , · ]) → 
  [] ≡ γ 
ηterm Γ [] = refl

term : Terminal' SubCat 
term = 
  record { 
    vertex = · ; 
    element = tt ; 
    universal = λ A → 
      record { 
        equiv-proof = λ tt → ([] , refl) , λ (v , p) → 
        ΣPathP (ηterm _ _ , λ _ _ → tt)} }

scwf : SCwF _ _ _ _
scwf .fst = SubCat
scwf .snd .fst = VTy
scwf .snd .snd .fst = vTm
scwf .snd .snd .snd .fst = term
scwf .snd .snd .snd .snd = {!   !}

open import Cubical.Categories.Monoidal.Instances.Presheaf
open PshMon SubCat ℓ-zero
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open EnrichedCategory
open import Cubical.Categories.Enriched.Functors.Base
open EnrichedFunctor

Ehom : CTy → CTy → ob 𝓟 
Ehom B B' .F-ob Γ = (Γ ◂ B ⊢k B') , {!   !}
Ehom B B' .F-hom = {!   !}
Ehom B B' .F-id = {!   !}
Ehom B B' .F-seq = {!   !}

stacks : EnrichedCategory 𝓟Mon  _ 
stacks .ob = CTy
stacks .Hom[_,_] = Ehom
stacks .id = {!   !}
stacks .seq = {!   !}
stacks .⋆IdL = {!   !}
stacks .⋆IdR = {!   !}
stacks .⋆Assoc = {!   !}

selfSCat = self SubCat ℓ-zero
𝓟[_,_] = 𝓟 .Hom[_,_]
stacks[_,_] = stacks .Hom[_,_]
self[_,_]  = selfSCat .Hom[_,_]

cTm' : ob stacks → ob selfSCat 
cTm' B .F-ob Γ = (Γ ⊢c B) , {!   !}
cTm' B .F-hom = subc
cTm' B .F-id = funExt subcId
cTm' B .F-seq = {!   !}

plug : (B B' : ob stacks) → 𝓟[ stacks[ B , B' ] , self[ cTm' B , cTm' B' ] ]
plug B B' = {!   !}

cTm : EnrichedFunctor 𝓟Mon stacks selfSCat
cTm .F-ob = cTm'
cTm .F-hom {B}{B'}= plug B B'
cTm .F-id = {!   !}
cTm .F-seq = {!   !}

CBPVDefSubst : CBPVModel _ _ _ _ _ _
CBPVDefSubst .Scwf = scwf
CBPVDefSubst .Stacks = stacks
CBPVDefSubst .CTm = cTm

{-}

clc : CTy → Type 
clc B = · ⊢c B 

clv : VTy → Type 
clv A = · ⊢v A 

data TermP : {B : CTy} → · ⊢c B → Type where 
  t-ret : {A : VTy}{v : · ⊢v A} → 
    TermP (ret v)
  t-lam : {A : VTy}{B : CTy}{m : (A ,, ·) ⊢c B} → 
    TermP (lam m)

Term : CTy → Type 
Term B = Σ[ m ∈ clc B ] TermP m

step :  {B : CTy} → clc B → Term B ⊎ clc B 
step (ret v) = inl ((ret v) , t-ret)
step (force (thunk m)) = inr m
step (lam m) = inl ((lam m) , t-lam)
step (app m v) = 
  ⊎rec 
    (λ {(.(lam _) , (t-lam{m = m})) → inr (subc (v ∷ []) m) }) 
    (λ m' → inr (app m' v)) 
    (step m)
step (rec× (pair v w) m) = inr (subc (v ∷ (w ∷ [])) m)
step (bind m n) = 
  ⊎rec 
    (λ {(.(ret _) , (t-ret{v = v})) → inr (subc (v ∷ []) n)}) 
    (λ m' → inr (bind m' n)) 
    (step m)



open import Cubical.CoData.Delay

open import Cubical.Categories.Category
open Category
open import  Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Foundations.Structure hiding(str)
open import Cubical.Categories.Limits.Terminal

hTerm : CTy → hSet ℓ-zero 
hTerm B = Term B , {!   !}

hclc : CTy → hSet ℓ-zero 
hclc B = (clc B) , {!   !}

coalg : (B : CTy) → ob (CoAlg (hTerm B)) 
coalg B = algebra (hclc B) step 


run' : (B : CTy) → CoAlg (hTerm B) [ coalg B , DelayCoAlg (hTerm B) ] 
run' B = terminalArrow (CoAlg (hTerm B)) (FinalCoAlg (hTerm B)) (coalg B)
open AlgebraHom 

run : {B : CTy} → clc B → Delay ⟨ hTerm B ⟩ 
run {B} m = run' B .carrierHom m

prog : clc (F one)
prog = bind (ret u) (app (lam (ret (var vz))) (var vz))

open import Cubical.Data.Nat 

poke : {A : Type} → ℕ → Delay A → A ⊎ Delay A 
poke zero d = inr d
poke (suc n) d = ⊎rec inl (poke n) (unfold d)
  

_ : poke 3 (run prog) ≡ inl ((ret u) , t-ret)
_ = refl
 
prog2 : clc (F one)
prog2 = bind (ret u) (app (force(thunk(lam (ret (var vz))))) (var vz))

_ : poke 4 (run prog2) ≡ inl ((ret u) , t-ret)
_ = refl
  
-}