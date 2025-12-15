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
-- add base types like sums
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
wksub {Δ}{Γ}{A} γ = mapOverIdfun (λ A v → renSubv (wkRen (idRen _)) v) _ γ

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

subk : Sub[ Δ , Γ ] → Γ ◂ B ⊢k B' → Δ ◂ B ⊢k B' 
subk γ varc = varc
subk γ (∙V v k) = ∙V (subv γ v) (subk γ k)
subk γ (x←∙:M k m) = x←∙:M (subk γ k) (subc (liftSub γ) m)

idSub : ∀ {Γ} → Sub[ Γ , Γ ]
idSub {[]} = []
idSub {x ∷ Γ} = (var vz) ∷ wksub idSub

_⋆Sub_ : Sub[ Θ , Δ ] → Sub[ Δ , Γ ] → Sub[ Θ , Γ ] 
δ ⋆Sub [] = []
δ ⋆Sub (x ∷ γ) = subv δ x ∷ (δ ⋆Sub γ)

_⋆k_ : {B₁ B₂ B₃ : CTy} → Γ ◂ B₁ ⊢k B₂ → Γ ◂ B₂ ⊢k B₃ → Γ ◂ B₁ ⊢k B₃ 
k ⋆k varc = k
k ⋆k ∙V v k' = ∙V v (k ⋆k k')
k ⋆k x←∙:M k' m = x←∙:M (k ⋆k k') m

⋆kId : {k : Γ ◂ B ⊢k B'} → k ≡ (varc ⋆k k) 
⋆kId {k = varc} = refl
⋆kId {k = ∙V x k} = cong₂ ∙V refl ⋆kId 
⋆kId {k = x←∙:M k x} = cong₂ x←∙:M ⋆kId refl

⋆kAssoc : {B₁ B₂ B₃ B₄ : CTy}
  {k₁ : Γ ◂ B₁ ⊢k B₂}
  {k₂ : Γ ◂ B₂ ⊢k B₃}
  {k₃ : Γ ◂ B₃ ⊢k B₄} → 
  ((k₁ ⋆k k₂) ⋆k k₃) ≡ (k₁ ⋆k (k₂ ⋆k k₃))
⋆kAssoc {k₃ = varc} = refl
⋆kAssoc {k₃ = ∙V x k₃} = cong₂ ∙V refl ⋆kAssoc
⋆kAssoc {k₃ = x←∙:M k₃ x} = cong₂ x←∙:M ⋆kAssoc refl

distrib : {γ : Sub[ Δ , Γ ]}
  {B₁ B₂ B₃ : CTy}
  {k : Γ ◂ B₁ ⊢k B₂}
  {k' : Γ ◂ B₂ ⊢k B₃} → 
  (subk γ k ⋆k subk γ k') ≡ subk γ (k ⋆k k')
distrib {k' = varc} = refl
distrib {k' = ∙V x k'} = cong₂ ∙V refl distrib
distrib {k' = x←∙:M k' x} = cong₂ x←∙:M distrib refl

s⟨_⟩∷⟨_⟩ :
  ∀ {x x' : Δ ⊢v A}{γ γ' : Sub[ Δ , Γ ]}
  → x ≡ x'
  → γ ≡ γ'
  → Path (Sub[ Δ , (A ∷ Γ)]) (x ∷ γ) (x' ∷ γ')
s⟨ x ⟩∷⟨ γ ⟩ i = x i ∷ γ i

indexWkSub : (γ : Sub[ Δ , Γ ])(x : Var Γ A) → 
  index (wksub γ) x ≡ renSubv (wkRen (idRen Δ)) (index γ x)
indexWkSub γ x = {!   !}

indexId : (x : Var Γ A) → index idSub x ≡ var x
indexId {Γ = A' ∷ Γ} {A = A} vz = refl
indexId {Γ = A' ∷ Γ} {A = A} (vs x) = {!   !}

subWkSub : ∀ (γ : Sub[ Δ , Γ ])(t : Γ ⊢v A) → 
  subv (wksub {A = A} γ) t ≡ renSubv (wkRen (idRen Δ)) (subv γ t)
subWkSub γ (var x) = indexWkSub _ _
subWkSub γ u = refl
subWkSub γ (pair t t₁) = cong₂ pair {! subWkSub γ t !} {!   !}
subWkSub γ (thunk x) = {!   !}

mutual 
  subvId : (v : Γ ⊢v A) → subv idSub v ≡ v 
  subvId (var x) = indexId x
  subvId u = refl
  subvId (pair v w) = cong₂ pair (subvId v) (subvId w)
  subvId (thunk m) = cong thunk (subcId m)

  subcId : (m : Γ ⊢c B) → subc idSub m ≡ m 
  subcId (ret v) = cong ret (subvId v)
  subcId (force v) = cong force (subvId v)
  subcId (lam m) = cong lam (subcId m)
  subcId (app m v) = cong₂ app (subcId m) (subvId v)
  subcId (rec× v m) = cong₂ rec× (subvId v) (subcId m)
  subcId (bind m n) = cong₂ bind (subcId m) (subcId n)

open import Cubical.Foundations.Function

-- Define subv⋆ and subc⋆ mutually
mutual
  subv⋆ : ∀ {Γ Δ Θ : Ctx} → (g : Sub[ Θ , Δ ]) (f : Sub[ Δ , Γ ])(x : Γ ⊢v A) → 
    subv (g ⋆Sub f) x ≡ (subv g ((subv f) x))
  subv⋆ g [] (var ())
  subv⋆ g (y ∷ f) (var vz) = refl
  subv⋆ g (y ∷ f) (var (vs x)) = subv⋆ g f (var x)
  subv⋆ g f u = refl
  subv⋆ g f (pair v w) = cong₂ pair (subv⋆ g f v) (subv⋆ g f w)
  subv⋆ g f (thunk m) = cong thunk (subc⋆ g f m)

  subc⋆ : ∀ {Γ Δ Θ : Ctx} → (g : Sub[ Θ , Δ ]) (f : Sub[ Δ , Γ ]) (m : Γ ⊢c B) → 
    subc (g ⋆Sub f) m ≡ (subc g (subc f m))
  subc⋆ g f (ret v) = cong ret (subv⋆ g f v)
  subc⋆ g f (force v) = cong force (subv⋆ g f v)
  subc⋆ g f (lam m) = cong lam {!  liftSub !} ∙ {!  liftSub !}
  subc⋆ g f (app m v) = cong₂ app (subc⋆ g f m) (subv⋆ g f v)
  subc⋆ g f (rec× v m) =  {!   !} --cong₂ rec× (subv⋆ g f v) (subc⋆ (liftSub (liftSub g)) (liftSub (liftSub f)) m)
  subc⋆ g f (bind m n) = {!   !} -- cong₂ bind (subc⋆ g f m) (subc⋆ (liftSub g) (liftSub f) n)

subvAssoc : (f : Sub[ Δ , Γ ]) (g : Sub[ Θ , Δ ]) →
  subv (g ⋆Sub f) ≡ (λ x₁ → subv g (subv f x₁))
subvAssoc f g = funExt (λ v → subv⋆ g f v)

subcAssoc : (f : Sub[ Δ , Γ ]) (g : Sub[ Θ , Δ ]) →
  subc (g ⋆Sub f) ≡ (λ x₁ → subc g (subc f x₁))
subcAssoc f g = funExt (λ v → subc⋆ g f v)

⋆Sub⋆IdL : (γ : Sub[ Δ , Γ ]) → 
  (idSub ⋆Sub γ) ≡ γ 
⋆Sub⋆IdL [] = refl
⋆Sub⋆IdL (v ∷ γ) = s⟨ subvId v ⟩∷⟨ ⋆Sub⋆IdL γ ⟩

⋆Sub⋆IdR : {Γ : Ctx} → (γ : Sub[ Δ , Γ ]) → 
  (γ ⋆Sub idSub) ≡ γ 
⋆Sub⋆IdR {Γ} [] = refl
⋆Sub⋆IdR (y ∷ γ) = s⟨ refl ⟩∷⟨ {!   !} ⟩

⋆Sub⋆Assoc : ∀ (f : Sub[ ξ , Θ ]) (g : Sub[ Θ , Δ ]) (h : Sub[ Δ , Γ ]) →
  ((f ⋆Sub g) ⋆Sub h) ≡ (f ⋆Sub (g ⋆Sub h))
⋆Sub⋆Assoc _ _ [] = refl
⋆Sub⋆Assoc f g (_∷_ {A} y h) = s⟨ {! funExt⁻ (subvAssoc g f) ?  !} ⟩∷⟨ ⋆Sub⋆Assoc _ _ _ ⟩

open import Cubical.Categories.CBPV.Base
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open Functor
open Category
open import Cubical.Categories.Limits.Terminal.More

SubCat : Category _ _ 
SubCat .ob = Ctx
SubCat .Hom[_,_] = Sub[_,_]
SubCat .id = idSub
SubCat ._⋆_ = _⋆Sub_
SubCat .⋆IdL = ⋆Sub⋆IdL
SubCat .⋆IdR = ⋆Sub⋆IdR
SubCat .⋆Assoc = ⋆Sub⋆Assoc
SubCat .isSetHom = {!   !}

vTm : VTy → Functor (SubCat ^op) (SET _)
vTm A .F-ob Γ = (Γ ⊢v A) , (λ _ _ → {!   !})
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
scwf .snd .snd .snd = term , (λ A Γ → {!   !})

open import Cubical.Categories.Monoidal.Instances.Presheaf
open PshMon SubCat ℓ-zero
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open EnrichedCategory
open import Cubical.Categories.Enriched.Functors.Base
open EnrichedFunctor
open import Cubical.Categories.NaturalTransformation.Base 
open NatTrans
open import Cubical.Categories.Presheaf.Morphism.Alt 
open PshHom

Ehom : CTy → CTy → ob 𝓟 
Ehom B B' .F-ob Γ = (Γ ◂ B ⊢k B') , (λ _ _ → {!   !})
Ehom B B' .F-hom = subk
Ehom B B' .F-id = {!   !}
Ehom B B' .F-seq = {!   !}

stacks : EnrichedCategory 𝓟Mon  _ 
stacks .ob = CTy
stacks .Hom[_,_] = Ehom
stacks .id .N-ob Γ tt* = varc
stacks .id .N-hom γ = funExt λ _ → refl
stacks .seq X Y Z .N-ob Γ (k , k') = k ⋆k k'
stacks .seq X Y Z .N-hom γ = goal where 
-- inline → termination issues
  goal : (λ x₁ → subk γ (x₁ .fst) ⋆k subk γ (x₁ .snd)) 
    ≡
    (λ x₁ → subk γ (x₁ .fst ⋆k x₁ .snd))
  goal = funExt λ (k , k') → distrib 
stacks .⋆IdL B B' = 
  makeNatTransPath (funExt λ Γ → funExt λ (_ , k) → ⋆kId)
stacks .⋆IdR B B' = 
  makeNatTransPath (funExt λ Γ → funExt λ (k , _) → refl)
stacks .⋆Assoc B₁ B₂ B₃ B₄ = 
  makeNatTransPath (funExt λ Γ → funExt λ (k₁ , (k₂ , k₃)) → ⋆kAssoc)

selfSCat = self SubCat ℓ-zero
𝓟[_,_] = 𝓟 .Hom[_,_]
stacks[_,_] = stacks .Hom[_,_]
self[_,_]  = selfSCat .Hom[_,_]

cTm' : ob stacks → ob selfSCat 
cTm' B .F-ob Γ = (Γ ⊢c B) , (λ _ _ → {!   !})
cTm' B .F-hom = subc
cTm' B .F-id = funExt subcId
cTm' B .F-seq f g = {!  subcAssoc f g   !}

plug' : {Γ : Ctx}{B B' : CTy} → Γ ◂ B ⊢k B' → Γ ⊢c B → Γ ⊢c B' 
plug' varc m = m
plug' (∙V v k) m = app (plug' k m) v
plug' (x←∙:M k n) m = bind (plug' k m) n

plug : (B B' : ob stacks) → 𝓟[ stacks[ B , B' ] , self[ cTm' B , cTm' B' ] ]
plug B B' .N-ob Γ k = pshhom (λ Δ (γ , m) → plug' (subk γ k) m) {!   !}
plug B B' .N-hom = {!   !} 

cTm : EnrichedFunctor 𝓟Mon stacks selfSCat
cTm .F-ob = cTm'
cTm .F-hom {B}{B'}= plug B B'
cTm .F-id = 
  makeNatTransPath (funExt λ Γ → funExt λ _ → 
    makePshHomPath (funExt λ Δ → funExt λ (γ , m) → refl))
cTm .F-seq = 
  makeNatTransPath (funExt λ Γ → funExt λ (k , k') → 
    makePshHomPath (funExt λ Δ → funExt λ (γ , m) →  
      {!   !} ))

CBPVDefSubst : CBPVModel _ _ _ _ _ _
CBPVDefSubst .fst  = scwf
CBPVDefSubst .snd .fst = stacks
CBPVDefSubst .snd .snd = cTm
