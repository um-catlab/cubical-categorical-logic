{-# OPTIONS --type-in-type #-}
-- collage levels suck
module HyperDoc.Operational.Model where

open import Cubical.Data.Sum 
open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Bifunctor 


open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import HyperDoc.Operational.Graph
open import HyperDoc.Lib

open Category
open Categoryᴰ
open Functor
open Functorᴰ
 
 
CBPVModel : (ℓV ℓV' ℓC ℓC' ℓG ℓG' : Level ) → Type _
CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG' = 
  Σ[ V ∈ Category ℓV ℓV' ] 
  Σ[ C ∈ Category ℓC ℓC' ] 
  BifunctorSep (V ^op) C (GRAPH ℓG ℓG')


module CBPVModelSyntax 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' : Level}
  (M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG') where 

  V = M .fst 
  C = M .snd .fst 
  O = M .snd .snd
  open BifunctorSep
  
  -- Pick one!
 -- OBif : Bifunctor (V ^op) C (pGRAPH ℓG ℓG')
 -- OBif = (mkBifunctorSep (M .snd .snd))

  OPar = BifunctorToParFunctor (mkBifunctorSep O)

  O[_,_] : ob V → ob C → ob (GRAPH ℓG ℓG') 
  O[_,_] A B = O .Bif-ob A  B

  

  O'[_,_] : ob V → ob C → Type ℓG
  O'[_,_] A B = O[ A , B ]  .fst .fst

  Node[_,_] : ob V → ob C → Type ℓG
  Node[_,_] = O'[_,_]

  _ = {!  O[_,_]  _ _  .fst .fst .fst !}

  _↦O_ : {A : ob V}{B : ob C} → (M M' : O'[ A , B ]) → Type ℓG' 
  _↦O_ {A}{B} M M' = ⟨ O[ A , B ] .snd M M' ⟩

  Edge[_,_] : {A : ob V}{B : ob C} → (M M' : O'[ A , B ]) → Type ℓG' 
  Edge[_,_] = _↦O_


  -- uhg.. lifts 
  open import Cubical.Data.Empty
  Collage : Category _ _ 
  Collage .ob = ob V ⊎ ob C
  Hom[ Collage  , inl v ] (inl v') = V [ v , v' ]
  Hom[ Collage  , inl v ] (inr c) = O'[ v , c ] 
  Hom[ Collage  , inr c ] (inl v) = ⊥
  Hom[ Collage  , inr c ] (inr c') = C [ c , c' ]
  Collage .id {inl x} = V .id
  Collage .id {inr x} = C .id
  _⋆_ (Collage) {inl x} {inl x₁} {inl x₂} f g = (V ⋆ f) g 
  _⋆_ (Collage) {inl x} {inl x₁} {inr x₂} f g = O .Bif-homL f x₂ .fst g -- lcomp f .carmap g
  _⋆_ Collage {inl x} {inr x₁} {inr x₂} f g = O .Bif-homR x g .fst f -- rcomp g  .carmap f
  _⋆_ Collage {inr x} {inr x₁} {inr x₂} f g = (C ⋆ f) g
  Collage .⋆IdL {inl x} {inl x₁} f = V .⋆IdL f
  Collage .⋆IdL {inl x} {inr x₁} f = {!  O'[ x , x₁ ]  !} -- lcompId
  Collage .⋆IdL {inr x} {inr x₁} f = C .⋆IdL f
  Collage .⋆IdR {inl x} {inl x₁} f = V .⋆IdR f
  Collage .⋆IdR {inl x} {inr x₁} f = {!   !} -- rcompId
  Collage .⋆IdR {inr x} {inr x₁} f = C .⋆IdR f
  Collage .⋆Assoc {inl x} {inl x₁} {inl x₂} {inl x₃} f g h = V .⋆Assoc f g h
  Collage .⋆Assoc {inl x} {inl x₁} {inl x₂} {inr x₃} f g h = {!   !} -- sym lcompSeq
  Collage .⋆Assoc {inl x} {inl x₁} {inr x₂} {inr x₃} f g h = {!   !} -- sym lrSeq
  Collage .⋆Assoc {inl x} {inr x₁} {inr x₂} {inr x₃} f g h = {!   !} -- rcompSeq
  Collage .⋆Assoc {inr x} {inr x₁} {inr x₂} {inr x₃} f g h = C .⋆Assoc f g h
  Collage .isSetHom {inl x} {inl x₁} = V. isSetHom
  Collage .isSetHom {inl x} {inr x₁} = O[ x , x₁ ] .fst .snd
  Collage .isSetHom {inr x} {inl x₁} ()
  Collage .isSetHom {inr x} {inr x₁} = C .isSetHom


CBPVMorphism : {ℓV ℓV' ℓC ℓC' ℓG ℓG' : Level}
  (M N : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG') → Type _
CBPVMorphism M N = 
  Σ[ Fv ∈ Functor M.V N.V ] 
  Σ[ Fc ∈ Functor M.C N.C ] 
  NatTrans M.OPar (N.OPar ∘F ((Fv ^opF) ×F Fc)) where 

  module M = CBPVModelSyntax M 
  module N = CBPVModelSyntax N

idModelMorphsim : 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' : Level} 
  (M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG') →  
  CBPVMorphism M M 
idModelMorphsim M .fst = Id
idModelMorphsim M .snd .fst = Id
idModelMorphsim M .snd .snd .NatTrans.N-ob (A , B) = (λ z → z) , (λ {n} {n'} z → z)
idModelMorphsim M .snd .snd .NatTrans.N-hom (V , S)= refl

module CBPVMorphismSyntax 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' : Level}
  {M N : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG'}
  (F : CBPVMorphism M N ) where

  FV = F .fst 
  FC = F .snd .fst 
  FO = F .snd .snd 


module _ 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' : Level}
  (M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG')
  (ℓVᴰ ℓVᴰ' ℓCᴰ ℓCᴰ' ℓGᴰ ℓGᴰ' : Level )
   where

  open CBPVModelSyntax M

  CBPVModelᴰ : Type _ 
  CBPVModelᴰ = 
    Σ[ Vᴰ ∈ Categoryᴰ  V ℓVᴰ ℓVᴰ' ]
    Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ ]  
    BifunctorSepᴰ (M .snd .snd) (Vᴰ ^opᴰ) Cᴰ (GRAPHᴰ ℓG ℓG' ℓGᴰ ℓGᴰ')



module CBPVModelᴰSyntax 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' : Level}
  {M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG'}
  {ℓVᴰ ℓVᴰ' ℓCᴰ ℓCᴰ' ℓGᴰ ℓGᴰ' : Level }
  (Mᴰ : CBPVModelᴰ M ℓVᴰ ℓVᴰ' ℓCᴰ ℓCᴰ' ℓGᴰ ℓGᴰ') where 

  open CBPVModelSyntax M
  open BifunctorSepᴰ (Mᴰ .snd .snd)

  Vᴰ = Mᴰ .fst 
  Cᴰ = Mᴰ .snd .fst 
  Oᴰ = Mᴰ .snd .snd 

  --OᴰBif : Bifunctorᴰ (ParFunctorToBifunctor O) (Vᴰ ^opᴰ) Cᴰ (pGRAPHᴰ ℓG ℓG' ℓGᴰ ℓGᴰ')
  --OᴰBif = ParFunctorᴰToBifunctorᴰ Oᴰ

  -- _⟪_⟫l
  -- Oᴰ'[ subC V M ][ vty A , cty B ]

  Oᴰ'[_][_,_] : {A : ob V}{B : ob C} → (O'[ A , B ])→ (Vᴰ .ob[_] A) → (Cᴰ .ob[_] B) → Type ℓGᴰ 
  Oᴰ'[_][_,_] {A}{B}M Aᴰ Bᴰ = Bif-obᴰ Aᴰ Bᴰ .fst M .fst

  Nodeᴰ[_][_,_] : {A : ob V}{B : ob C} → (O'[ A , B ])→ (Vᴰ .ob[_] A) → (Cᴰ .ob[_] B) → Type ℓGᴰ 
  Nodeᴰ[_][_,_] = Oᴰ'[_][_,_]

  _◂_↦Oᴰ_ : {A : ob V}{B : ob C}{Aᴰ : Vᴰ .ob[_] A}{Bᴰ : Cᴰ .ob[_] B}{M M' : O'[ A , B ]} →  
    (e :  M ↦O M' ) → Oᴰ'[ M ][ Aᴰ , Bᴰ ] → Oᴰ'[ M' ][ Aᴰ , Bᴰ ] → Type ℓGᴰ'  
  _◂_↦Oᴰ_ {A}{B}{Aᴰ}{Bᴰ}{M}{M'} e P Q = 
    Bif-obᴰ Aᴰ  Bᴰ .snd {M}{M'} e P Q  .fst

  Edgeᴰ[_][_,_] : {A : ob V}{B : ob C}{Aᴰ : Vᴰ .ob[_] A}{Bᴰ : Cᴰ .ob[_] B}{M M' : O'[ A , B ]} →  
    (e :  M ↦O M' ) → Oᴰ'[ M ][ Aᴰ , Bᴰ ] → Oᴰ'[ M' ][ Aᴰ , Bᴰ ] → Type ℓGᴰ'  
  Edgeᴰ[_][_,_] = _◂_↦Oᴰ_

{-}
  isProp◂↦Oᴰ : {A : ob V}{B : ob C}{Aᴰ : Vᴰ .ob[_] A}{Bᴰ : Cᴰ .ob[_] B}{M M' : O'[ A , B ]} →  
    {e :  M ↦O M' }{P : Oᴰ'[ M ][ Aᴰ , Bᴰ ]}{Q : Oᴰ'[ M' ][ Aᴰ , Bᴰ ]} → 
    (prf prf' : e ◂ P ↦Oᴰ Q) → prf ≡ prf'
  isProp◂↦Oᴰ {A}{B}{Aᴰ}{Bᴰ}{M}{M'}{e}{P}{Q} prf prf' = 
    Bif-obᴰ Aᴰ Bᴰ  .snd {M}{M'}{e}{P}{Q} prf prf'-}


  Collageᴰ : Categoryᴰ Collage _ _
  Collageᴰ .ob[_] (inl A) = Vᴰ .ob[_] A
  Collageᴰ .ob[_] (inr B) = Cᴰ .ob[_] B
  Hom[_][_,_] Collageᴰ {inl A} {inl A'} = Vᴰ .Hom[_][_,_]
  Hom[_][_,_] Collageᴰ {inl A} {inr B} M aᴰ bᴰ = Oᴰ'[ M ][ aᴰ , bᴰ ] 
  Hom[_][_,_] Collageᴰ {inr B} {inl A} ()
  Hom[_][_,_] Collageᴰ {inr B} {inr B'} = Cᴰ .Hom[_][_,_]
  Collageᴰ .idᴰ {inl x} = Vᴰ .idᴰ
  Collageᴰ .idᴰ {inr x} = Cᴰ .idᴰ
  _⋆ᴰ_ Collageᴰ {inl A} {inl A'} {inl A''} = Vᴰ ._⋆ᴰ_
  _⋆ᴰ_ Collageᴰ {inl A} {inl A'} {inr B} {f}{g}{Aᴰ}{Bᴰ}{Cᴰ} fᴰ Mᴰ = Bif-homLᴰ fᴰ Cᴰ .fst g Mᴰ 
  _⋆ᴰ_ Collageᴰ {inl A} {inr B} {inr B'} {f}{g}{Aᴰ}{Bᴰ}{Cᴰ} Mᴰ gᴰ = Bif-homRᴰ gᴰ Aᴰ .fst f Mᴰ 
  _⋆ᴰ_ Collageᴰ {inr B} {inr B'} {inr B''} = Cᴰ ._⋆ᴰ_
  Collageᴰ .⋆IdLᴰ {inl x} {inl x₁} = Vᴰ .⋆IdLᴰ
  Collageᴰ .⋆IdLᴰ {inl x} {inr x₁} = {!   !}
  Collageᴰ .⋆IdLᴰ {inr x} {inr x₁} = Cᴰ .⋆IdLᴰ
  Collageᴰ .⋆IdRᴰ {inl x} {inl x₁} = Vᴰ .⋆IdRᴰ
  Collageᴰ .⋆IdRᴰ {inl x} {inr x₁} = {!   !}
  Collageᴰ .⋆IdRᴰ {inr x} {inr x₁} = Cᴰ .⋆IdRᴰ
  Collageᴰ .⋆Assocᴰ = {!   !}
  Collageᴰ .isSetHomᴰ = {!   !}


  open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
  -- cartesian lifts over obliques
  -- except the displayed collage forgets the enriched structure
  ForgetfulObliqueLifts : Type 
  ForgetfulObliqueLifts = 
    {A : ob V}{B : ob C}(M : O'[ A , B ])
    (Bᴰ : Cᴰ .ob[_] B) → CartesianLift Collageᴰ {inl A}{inr B} M Bᴰ

  ForgetfulObliqueOpLifts : Type 
  ForgetfulObliqueOpLifts = 
    {A : ob V}{B : ob C}(M : O'[ A , B ])
    (Aᴰ : Vᴰ .ob[_] A) → CartesianLift (Collageᴰ ^opᴰ) {inr B}{inl A} M Aᴰ


{- 
open Category
open Functor
-- open TSystem 
record CBPVModel : Type where 
  field 
    V : Category _ _ 
    C : Category _ _ 
    O : Functor ((V ^op) ×C C) TSysCat

  O[_,-] : (v : ob V) → Functor C TSysCat
  O[_,-] v = O ∘F rinj _ _ v

  O[_,_] : ob V → ob C → ob TSysCat
  O[_,_] v c = O .F-ob (v , c)

  O'[_,_] : ob V → ob C → Type 
  O'[_,_] v c = ?
    -- ⟨  O .F-ob (v , c)  .state ⟩ 


record CBPVMorphism (M N : CBPVModel) : Type where
  private 
    module M = CBPVModel M 
    module N = CBPVModel N
  field 
    FV : Functor M.V N.V 
    FC : Functor M.C N.C 
    FO : NatTrans M.O (N.O ∘F ((FV ^opF) ×F FC)) 

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor 
open import Cubical.Categories.Displayed.BinProduct 

record CBPVModelᴰ (M : CBPVModel) : Type where 
  module M = CBPVModel M
  field 
    Vᴰ : Categoryᴰ M.V _ _
    Cᴰ : Categoryᴰ M.C _ _
    Oᴰ : Functorᴰ M.O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) ? --  TSysCatᴰ 

open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.HomFunctor
open import HyperDoc.Lib

Hom^op :  Functor ((POSET _ _) ×C (POSET _ _)^op) (SET _)
Hom^op  = (HomFunctor _) ∘F Cubical.Categories.Constructions.BinProduct.Sym
  
{-.F-ob (P , Q) = (POSET _ _) [ Q , P ] , (POSET _ _) .isSetHom
Hom^op .F-hom {(A , B)}{(A' , B')} (f , g) h = MonComp g (MonComp h f)
Hom^op .F-id = funExt λ _ → eqMon _ _ refl
Hom^op .F-seq _ _ = funExt λ _ → eqMon _ _ refl
-}

FORGET : Functor (TSysCat) (SET _) 
FORGET .F-ob S = state  S
FORGET .F-hom f = f .TSystem[_,_].tmap
FORGET .F-id = refl
FORGET .F-seq _ _ = refl

open import HyperDoc.Syntax
open NatTrans

record Logic (M : CBPVModel ) : Type _ where 
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

open Categoryᴰ
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
  (M : CBPVModel)
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
  open import Cubical.Data.Maybe
  open import Cubical.Data.Unit
  open import Cubical.Categories.Displayed.Instances.Sets
  open MonFun renaming (f to fun)

  Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) TSysCatᴰ
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .TSystemᴰ.stateᴰ M = A VL.◂ P ≤ (pull M $ Q) , isProp→isSet VL.isProp≤
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .TSystemᴰ.transᴰ M prf with (O[ A , B ] .trans M)  
  ... | nothing = tt
  ... | just M' = goal where
    have : O'[ A , B ] 
    have = M

    have' : A VL.◂ P ≤ (pull M $ Q)
    have' = prf

    goal : A VL.◂ P ≤ (pull M' $ Q)
    goal = {!   !} 
    
  Oᴰ .Functorᴰ.F-homᴰ (Vᴰ , Sᴰ) .TSysᴰ[_][_,_].tmapᴰ = {!   !}
  Oᴰ .Functorᴰ.F-idᴰ = {!   !}
  Oᴰ .Functorᴰ.F-seqᴰ = {!   !}

  {- 
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

  -}

-}