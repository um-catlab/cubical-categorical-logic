{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Unary where 

open import Cubical.Data.List 
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.FinData
open import Cubical.Data.Maybe
open import Cubical.Data.Maybe.More

import Cubical.Data.Equality as Eq

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets

open import HyperDoc.Lib
open import HyperDoc.Operational.TypeStructure

open Category
open Functor

module Syntax where

  mutual 
    data VTy : Type  where 
      𝟙 Ans : VTy 
      U : CTy → VTy 

    data CTy : Type  where
      F : VTy → CTy    

  data _⊢v_ : (A A' : VTy) → Type  
  data _⊢c_ : (A : VTy)(B : CTy) → Type  
  data _⊢k_ : (B B' : CTy) → Type  

  data _⊢v_   where
    var : ∀{A}  → A ⊢v A
    tt : ∀{A} → A ⊢v 𝟙
    yes : ∀{A} → A ⊢v Ans 
    no : ∀{A} → A ⊢v Ans 
    thunk : ∀{A B} → A ⊢c B → A ⊢v U B

  data _⊢c_ where   
    ret : ∀{A A'} → A ⊢v A' → A ⊢c F A'
    bind : ∀{A A' B} → A ⊢c F A' → A' ⊢c B → A ⊢c B
    force : ∀{A B} →  A ⊢v U B → A ⊢c B    

  data _⊢k_ where 
    hole : ∀{B} → B ⊢k B
    bindk : ∀{A B B'} → B ⊢k F A → A ⊢c B' → B ⊢k B'


  mutual 
    subV : {A A' A'' : VTy} → A ⊢v A' → A' ⊢v A'' → A ⊢v A'' 
    subV V var = V
    subV V tt = tt
    subV V yes = yes
    subV V no = no
    subV V (thunk M) = thunk (subC V M)

    subC : {A A' : VTy}{B : CTy} → A' ⊢v A → A ⊢c B → A' ⊢c B 
    subC V (ret W) = ret (subV V W)
    subC V (bind M N) = bind (subC V M) N
    subC V (force W) = force (subV V W)

    plug : {A : VTy}{B B' : CTy} → B ⊢k B' → A ⊢c B → A ⊢c B'
    plug hole M = M
    plug (bindk S M) N = bind (plug S N) M

    kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B'' 
    kcomp S hole = S
    kcomp S (bindk S' M) = bindk (kcomp S S') M

    subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
    subVIdl var = refl
    subVIdl tt = refl
    subVIdl yes = refl
    subVIdl no = refl
    subVIdl (thunk M) = cong thunk (subCId M)

    subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
      subV (subV V W) Y ≡ subV V (subV W Y)
    subVAssoc V W var = refl
    subVAssoc V W tt = refl
    subVAssoc V W yes = refl
    subVAssoc V W no = refl
    subVAssoc V W (thunk M) = cong thunk (sym (subDist V W M))

    subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
    subVIdr V = refl

    subCId : ∀ {A B}(M : A ⊢c B) → subC (var {A}) M ≡ M
    subCId (ret V) = cong ret (subVIdl V)
    subCId (bind M N) = cong₂ bind (subCId M) refl
    subCId (force V) = cong force (subVIdl V)

    kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
    kcompIdl hole = refl
    kcompIdl (bindk M x) = cong₂ bindk (kcompIdl M) refl

    kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
    kcompIdr M = refl

    kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
      kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)
    kcompAssoc M N hole = refl
    kcompAssoc M N (bindk P x) = cong₂ bindk (kcompAssoc M N P) refl

    plugId : ∀ {A B}(M : A ⊢c B) → plug (hole {B}) M ≡ M
    plugId M = refl

    plugDist : ∀ {A B B' B''}(S : B ⊢k B')(S' : B' ⊢k B'')(M : A ⊢c B) → 
      plug S' (plug S M) ≡ plug (kcomp S S') M
    plugDist S hole M = refl
    plugDist S (bindk S' x) M = cong₂ bind (plugDist S S' M) refl

    subDist : ∀ {A A' A'' B}(V : A ⊢v A')(V' : A' ⊢v A'')(M : A'' ⊢c B) → --lcomp
      subC V (subC V' M) ≡ subC (subV V V') M
    subDist V V' (ret x) = cong ret (sym (subVAssoc V V' x ))
    subDist V V' (bind M M₁) = cong₂ bind (subDist V V' M) refl
    subDist V V' (force x) = cong force (sym (subVAssoc V V' x ))
  
    plugSub : ∀ {A A' B B'}(V : A ⊢v A')(M : A' ⊢c B)(S : B ⊢k B') → 
      subC V (plug S M) ≡ plug S (subC V M)
    plugSub V M hole = refl
    plugSub V M (bindk S x) = cong₂ bind (plugSub V M S) refl

open Syntax
open import HyperDoc.Operational.Model
open import HyperDoc.Operational.TransitionSystemAlt

V : Category ℓ-zero ℓ-zero
V .ob = VTy
V .Hom[_,_] = _⊢v_
V .id = var
V ._⋆_ = subV
V .⋆IdL = subVIdl
V .⋆IdR = subVIdr
V .⋆Assoc = subVAssoc
V .isSetHom = {!   !}

C : Category ℓ-zero ℓ-zero 
C .ob = CTy
C .Hom[_,_] = _⊢k_
C .id = hole
C ._⋆_ = kcomp
C .⋆IdL = kcompIdl
C .⋆IdR = kcompIdr
C .⋆Assoc = kcompAssoc
C .isSetHom = {!   !}

{-}
data isTerminal : ∀ {A B} → (A ⊢c B) → Type where 
  retTerm : ∀ {A A'} → (V : A ⊢v A') → isTerminal (ret V)

Terminal : VTy → CTy → Type 
Terminal A B = Σ[ M ∈ A ⊢c B ] isTerminal M

data isRedex : ∀ {A B} → (A ⊢c B) → Type where 
  forceThunk : ∀ {A B}{M : A ⊢c B} → isRedex (force (thunk M)) 
  bindRet : ∀ {Γ A B}{V : Γ ⊢v A}{M : A ⊢c B} → isRedex (bind (ret V) M) 


Redex : VTy → CTy → Type 
Redex A B = Σ[ M ∈ A ⊢c B ] isRedex M

data isRedexAt {B : CTy} : {A : VTy} → A ⊢c B → Type where
  atHole : ∀ {A}{trm : A ⊢c B} → isRedex trm → isRedexAt trm
  -- the redex is under a bind, the stack is explicitly bindk
  atBind : ∀ {Γ A} {M : Γ  ⊢c F A} {N : A ⊢c B} →  isRedexAt {F A} M 
    → isRedexAt {B} (bind M N) 
         --  → isRedexAt M → isRedexAt (bind M N)

RedexInCtx : VTy → CTy → Type 
RedexInCtx A B = Σ[ M ∈ A ⊢c B ] isRedexAt M


classify' : ∀{A B} → (M : A ⊢c B) → isTerminal M ⊎ isRedexAt M 
classify' (ret V) = inl (retTerm V)
classify' (bind (ret V) M) = inr (atHole bindRet) 
classify' (bind (bind M N) P) with (classify' (bind M N))
... | inr M' = inr (atBind {M = (bind M N)} {P} M')
classify' (bind (force M) N) with (classify' (force M)) 
... | inr M' = inr (atBind {M = force M}{N} M')
classify' (force (thunk M)) = inr (atHole forceThunk) 
classify' (force {U B}{B}(var {U B})) = {!  !}

red' : (A : VTy)(B : CTy) → RedexInCtx A B → Terminal A B ⊎ RedexInCtx A B 
red' A B = {!   !}


Sys : (A : VTy)(B : CTy) → TSystem _ 
Sys A B .TSystem.term = Terminal A B , {!   !}
Sys A B .TSystem.redex = RedexInCtx A B , {!   !}
Sys A B .TSystem.red = red' A B
-}

step' : (A : VTy)(B : CTy) → A ⊢c B → Maybe (A ⊢c B) 
step' A B (ret x) = nothing
step' A B (bind (ret V) M) = just (subC V M)
step' A B (bind M N) with step' _ _ M
... | nothing = nothing
... | just M' = just (bind M' N)
step' A B (force (thunk V)) = just V 
-- a stuck term
step' A B (force var) = nothing

Sys : (A : VTy)(B : CTy) → TSystem _ 
Sys A B .TSystem.state = (A ⊢c B) , {!   !}
Sys A B .TSystem.trans = step' A B

open TSystem[_,_]
import      Cubical.Data.Equality as Eq
data _↦_  : {A : VTy}{B : CTy} → A ⊢c B → A ⊢c B → Type where   
  Fβ :  ∀{A A' B} →  {V : A ⊢v A'}{M : A' ⊢c B}{N : A ⊢c B} →  
    Eq._≡_ N (subC V M) → 
    bind (ret V) M ↦ N  

  Uβ : ∀ {A B} {M : A ⊢c B} → force (thunk M) ↦ M

  bcong : ∀ {A A' B} {M M' : A ⊢c F A'}{N : A' ⊢c B}  →  M ↦ M' → bind M N ↦ bind M' N 

lemma : ∀ {A B B'} → {M N : A ⊢c B} (S : B ⊢k B') → M ↦ N  → plug S M ↦ plug S N 
lemma {A} {B} {B'} {M} {N} hole (Fβ Eq.refl) = Fβ Eq.refl
lemma {A} {B} {B'} {M} {N} (bindk S x) (Fβ Eq.refl) = bcong (lemma S (Fβ Eq.refl))
lemma {A} {B} {B'} {M} {N} hole Uβ = Uβ
lemma {A} {B} {B'} {M} {N} (bindk S x) Uβ = bcong (lemma S Uβ)
lemma {A} {B} {B'} {M} {N} hole (bcong prf) = lemma (bindk hole _) prf
lemma {A} {B} {B'} {M} {N} (bindk S x) (bcong prf) = bcong (lemma S (lemma (bindk hole _) prf))

lemma' : ∀ {A A' B } → {M N : A ⊢c B} (V : A' ⊢v A) → M ↦ N  → subC V M ↦ subC V N
lemma' {A} {A'} {B} {M} {N} var (Fβ{V = V'}{M'} Eq.refl) = subst (λ h → bind (ret (subV var V')) M' ↦ h) (sym (subDist var V' M')) (Fβ Eq.refl)
lemma' {A} {A'} {B} {M} {N} var Uβ = Uβ
lemma' {A} {A'} {B} {M} {N} var (bcong prf) = bcong (lemma' var prf)
lemma' {A} {A'} {B} {M} {N} tt (Fβ{V = V'}{M'} Eq.refl) = subst (λ h → bind (ret (subV tt V')) M' ↦ h) (sym (subDist tt V' M')) (Fβ Eq.refl)
lemma' {A} {A'} {B} {M} {N} tt Uβ = Uβ
lemma' {A} {A'} {B} {M} {N} tt (bcong prf) = bcong (lemma' tt prf)
lemma' {A} {A'} {B} {M} {N} yes (Fβ{V = V'}{M'} Eq.refl) = subst (λ h → bind (ret (subV yes V')) M' ↦ h) (sym (subDist yes V' M')) (Fβ Eq.refl) 
lemma' {A} {A'} {B} {M} {N} yes Uβ = Uβ
lemma' {A} {A'} {B} {M} {N} yes (bcong prf) = bcong (lemma' yes prf)
lemma' {A} {A'} {B} {M} {N} no (Fβ{V = V'}{M'} Eq.refl) = subst (λ h → bind (ret (subV no V')) M' ↦ h) (sym (subDist no V' M')) (Fβ Eq.refl)
lemma' {A} {A'} {B} {M} {N} no Uβ = Uβ
lemma' {A} {A'} {B} {M} {N} no (bcong prf) = bcong (lemma' no prf)
lemma' {A} {A'} {B} {M} {N} (thunk x) (Fβ{V = V'}{M'} Eq.refl) = subst (λ h → bind (ret (subV (thunk x) V')) M' ↦ h) (sym (subDist (thunk x) V' M')) (Fβ Eq.refl)
lemma' {A} {A'} {B} {M} {N} (thunk x) Uβ = Uβ
lemma' {A} {A'} {B} {M} {N} (thunk x) (bcong prf) = bcong (lemma' (thunk x) prf)

cor : ∀ {A A' B B'} → {M N : A ⊢c B}(V : A' ⊢v A)(S : B ⊢k B') → M ↦ N → subC V (plug S M) ↦ subC V (plug S N) 
cor {A}{A'}{B}{B'}{M}{N} V S prf = lemma' {A} {A'}{B'} {plug S M}{plug S N} V (lemma S prf)


open TSystem

SysHom : ∀ {A A' B B'} → A' ⊢v A → B ⊢k B' → TSystem[ Sys A B , Sys A' B' ]
SysHom V S .tmap M = subC V (plug S M)
SysHom {A}{A'}{B}{B'} V S .comm {M} with canStep? (Sys A B) M
... | inl x = {!  reflcanStep? !}
... | inr x = {!   !}
{- {ret x} = tt*
SysHom V S .comm {bind s s₁} with step' _ _ s 
... | nothing = {!   !}
... | just x = {!   !}
SysHom V S .comm {force var} = tt*
SysHom V S .comm {force (thunk w)} = {!   !}
 -}

Syn : CBPVModel 
Syn .CBPVModel.V = V
Syn .CBPVModel.C = C
Syn .CBPVModel.O .F-ob (A , B) = Sys A B
Syn .CBPVModel.O .F-hom {(A , B)}{(A' , B')} (V , S)= SysHom V S
Syn .CBPVModel.O .F-id = TSysMap≡ (funExt λ M → subCId _)
Syn .CBPVModel.O .F-seq (V , S) (V' , S')= 
  TSysMap≡ (funExt λ M → sym (subDist V' _ _ ) 
  ∙ cong₂ subC refl (cong₂ subC refl (sym (plugDist S S' M))  ∙ plugSub V _ S'))


SetModel : CBPVModel 
SetModel .CBPVModel.V = SET _
SetModel .CBPVModel.C = TSysCat
SetModel .CBPVModel.O .F-ob (A , B) .state = (⟨ A ⟩ → ⟨ B .state ⟩) , {!   !}
SetModel .CBPVModel.O .F-ob (A , B) .trans = just
SetModel .CBPVModel.O .F-hom = {!   !}
SetModel .CBPVModel.O .F-id = {!   !}
SetModel .CBPVModel.O .F-seq = {!   !}

open import Cubical.Categories.NaturalTransformation
open CBPVModel using (O[_,-])

GS : CBPVMorphism Syn SetModel 
GS .CBPVMorphism.FV = V [ 𝟙 ,-]
GS .CBPVMorphism.FC = O[_,-] Syn 𝟙
GS .CBPVMorphism.FO .NatTrans.N-ob (A , B) .tmap M V = ?
GS .CBPVMorphism.FO .NatTrans.N-ob (A , B) .comm = {!   !}
GS .CBPVMorphism.FO .NatTrans.N-hom = {!   !}