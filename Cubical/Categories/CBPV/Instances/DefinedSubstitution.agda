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
open import Cubical.Data.Sum renaming (rec to ⊎rec)


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


clc : CTy → Type 
clc B = · ⊢c B 

clv : VTy → Type 
clv A = · ⊢v A 

data CanStep : {B : CTy} → (m : clc B) → Type where 
  s-force-thunk : {B : CTy}{m : clc B} → 
    CanStep (force (thunk m))
  s-app-lam : {A : VTy}{B : CTy}{v : clv A}{m : (A ,, []) ⊢c B} → 
    CanStep (app (lam m) v)
  s-bind-ret : {A : VTy}{B : CTy}{v : clv A}{m : (A ,, []) ⊢c B} → 
    CanStep (bind (ret v) m)
  s-rec×-pair : {A A' : VTy}{B : CTy}{v : clv A}{w : clv A'}
    {m : (A ,, (A' ,, [])) ⊢c B} → 
    CanStep (rec× (pair v w) m)

open import  Cubical.Relation.Nullary

canStep : {B : CTy} → (m : clc B) → Dec (CanStep m) 
canStep (ret x) = no λ ()
canStep (force (thunk x)) = yes s-force-thunk
canStep (lam m) = no λ ()
canStep (app (force x₁) x) = no λ ()
canStep (app (lam m) x) = yes s-app-lam
canStep (app (app m x₁) x) = no λ ()
canStep (app (rec× x₁ m) x) = no λ ()
canStep (app (bind m m₁) x) = no λ ()
canStep (rec× (pair x x₁) m) = yes s-rec×-pair
canStep (bind (ret x) m₁) = yes s-bind-ret
canStep (bind (force x) m₁) = no λ ()
canStep (bind (app m x) m₁) = no λ ()
canStep (bind (rec× x m) m₁) = no λ ()
canStep (bind (bind m m₂) m₁) = no λ ()

Terminals : CTy → Type 
Terminals B = Σ[ m ∈ clc B ] ¬ (CanStep m)

step' : {B : CTy}{m : clc B}→ CanStep m → clc B 
step' (s-force-thunk {m = m}) = m
step' (s-app-lam {v = v}{m}) = subc (v ∷ []) m
step' (s-bind-ret{v = v}{m}) = subc (v ∷ []) m
step' (s-rec×-pair{v = v}{w}{m}) = subc (v ∷ (w ∷ [])) m
open import Cubical.Foundations.Function

step : {B : CTy} → clc B → (Terminals B) ⊎ (clc B)
step m = decRec (inr ∘S step') (λ p → inl (m , p)) (canStep m)


open import Cubical.CoData.Delay

open import Cubical.Categories.Category
open Category
open import  Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Foundations.Structure hiding(str)

open import Cubical.Data.Sigma
open import Cubical.Categories.Limits.Terminal

Term : CTy → hSet ℓ-zero 
Term B = Terminals B , {!   !}

clc' : CTy → hSet ℓ-zero 
clc' B = (clc B) , {!   !}

coalg : (B : CTy) → ob (CoAlg (Term B))
coalg B = algebra (clc' B) step 

run' : (B : CTy) → CoAlg (Term B) [ coalg B , DelayCoAlg (Term B) ] 
run' B = terminalArrow (CoAlg (Term B)) (FinalCoAlg (Term B)) (coalg B)
open AlgebraHom 

run : {B : CTy} → clc B → Delay ⟨ Term B ⟩ 
run {B} m = run' B .carrierHom m

prog : clc (F one)
prog = bind (ret u) (app (lam (ret (var vz))) (var vz))

open import Cubical.Data.Nat 

poke : {A : Type} → ℕ → Delay A → A ⊎ Delay A 
poke zero d = unfold d
poke (suc n) d = ⊎rec inl (poke n) (unfold d)


_ : poke 2 (run prog) ≡ (inl (ret u , (λ ())))
_ = refl

