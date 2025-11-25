{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

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
open import Cubical.Data.Sum


Sub[_,_] : Ctx → Ctx → Type 
Sub[_,_] Δ = ListP (Δ ⊢v_)

private
  variable
    A A' X Y : VTy
    B B' : CTy
    Δ Δ' Γ Θ Ξ : Ctx
    γ δ θ : Sub[ Δ , Γ ]

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

⋆Sub⋆IdL : (γ : Sub[ Δ , Γ ]) → 
  (idSub ⋆Sub γ) ≡ γ 
⋆Sub⋆IdL [] = refl
⋆Sub⋆IdL (v ∷ γ) = s⟨ subvId v ⟩∷⟨ ⋆Sub⋆IdL γ ⟩



data Term : {B : CTy} → · ⊢c B → Type where 
  t-ret : {A : VTy}{v : · ⊢v A} → 
    Term (ret v)
  t-lam : {A : VTy}{B : CTy}{m : (A ,, ·) ⊢c B} → 
    Term (lam m)

data Stuck : {B : CTy} → (m : · ⊢c B) → Type where
  -- application stuck forms
  s-app-force :
    {A : VTy} {B : CTy}
    {f : · ⊢v U (fun A B)}
    {v : · ⊢v A} →
    Stuck (app (force f) v)

  s-app-app :
    {A A' : VTy} {B : CTy}
    {m  : · ⊢c fun A (fun A' B)}
    {v : · ⊢v A}
    {w  : · ⊢v A'} →
    Stuck (app (app m v) w)

  s-app-rec× :
    {A A' A'' : VTy} {B : CTy}
    {p : · ⊢v (prod A A')}
    {m : (A ,, (A' ,, ·)) ⊢c fun A'' B}
    {x : · ⊢v A''} →
    Stuck (app (rec× p m) x)

  s-app-bind :
    {A A' : VTy} {B : CTy}
    {m  : · ⊢c F A'}
    {n : (A' ,, ·) ⊢c fun A B}
    {x  : · ⊢v A} →
    Stuck (app (bind m n) x)

  -- bind stuck forms
  s-bind-force :
    {A : VTy} {B : CTy}
    {u : · ⊢v U (F A)}
    {k : (A ,, ·) ⊢c B} →
    Stuck (bind (force u) k)

  s-bind-app :
    {A A' : VTy} {B : CTy}
    {m : · ⊢c fun A' (F A)}
    {v : · ⊢v A'}
    {k : (A ,, ·) ⊢c B} →
    Stuck (bind (app m v) k)

  s-bind-rec× :
    {A₁ A₂ A' : VTy} {B : CTy}
    {p : · ⊢v (prod A₁ A₂)}
    {m : (A₁ ,, (A₂ ,, ·)) ⊢c F A'}
    {k : (A' ,, ·) ⊢c B} →
    Stuck (bind (rec× p m) k)

  s-bind-bind :
    {A A' : VTy} {B : CTy}
    {m  : · ⊢c F A}
    {n : (A ,, ·) ⊢c F A'}
    {k  : (A' ,, ·) ⊢c B} →
    Stuck (bind (bind m n) k)

step : {B : CTy} → (m : · ⊢c B) → (Term m ⊎ Stuck m) ⊎ (· ⊢c B) 
-- steps
step (force (thunk m)) = inr m
step (app (lam m) v) = inr (subc (v ∷ []) m)
step (bind (ret v) m) = inr (subc (v ∷ []) m)
step (rec× (pair v w) m) = inr (subc (v ∷ (w ∷ [])) m)

-- terminal
step (ret x) = inl (inl t-ret) 
step (lam m) = inl (inl t-lam)

-- stuck terms
step (app (force x₁) x) = inl (inr s-app-force)
step (app (app m x₁) x) = inl (inr s-app-app)
step (app (rec× x₁ m) x) = inl (inr s-app-rec×)
step (app (bind m m₁) x) = inl (inr s-app-bind)
step (bind (force x) m₁) = inl (inr s-bind-force)
step (bind (app m x) m₁) = inl (inr s-bind-app)
step (bind (rec× x m) m₁) = inl (inr s-bind-rec×)
step (bind (bind m m₂) m₁) = inl (inr s-bind-bind) 
