module HyperDoc.AsDisplayed where 

open import Cubical.Data.Sigma 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Category 
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Posets.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.BinProduct 
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Categories.Displayed.Reasoning

open import HyperDoc.Syntax
open import HyperDoc.CBPVLogic
open import HyperDoc.CBPVModel
open import HyperDoc.Lib

open Category
open Categoryᴰ
open Functorᴰ
open Functor

-- demonstrating that our proof irrelevant model 
-- lines up with the proof relevant version
module convert 
  {ℓ ℓ' ℓP ℓP' : Level}{C : Category ℓ ℓ'}
  (F : Functor (C ^op) (POSET ℓP ℓP')) where 

  open HDSyntax F  

  Cᴰ : Categoryᴰ C ℓP ℓP' 
  ob[ Cᴰ ] = F∣_∣
  Cᴰ .Hom[_][_,_] {x}{y} f Fx Fy = x ◂ Fx ≤ f* f  Fy
  Cᴰ .idᴰ = eqTo≤  (sym f*id)
  Cᴰ ._⋆ᴰ_ {f = f} {g} = seq* f g
  Cᴰ .⋆IdLᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆IdRᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆Assocᴰ _ _ _ = toPathP (isProp≤ _ _)
  Cᴰ .isSetHomᴰ = isProp→isSet isProp≤ 

module _ 
  {ℓV ℓV' ℓC ℓC' ℓS ℓP ℓP' ℓR : Level}
  (M : Model ℓV ℓV' ℓC ℓC' ℓS)
  (L : CBPVLogic M ) where 

  open Model M 
  open CBPVLogic L

  Vᴰ : Categoryᴰ V ℓV ℓV 
  Vᴰ = convert.Cᴰ HL

  Cᴰ : Categoryᴰ C ℓV ℓV 
  Cᴰ = Cᴰ^op^op (Pred ^opᴰ) where 
    open convert {C = C ^op} (HC ∘F from^op^op) renaming(Cᴰ to Pred)

  module VL = HDSyntax HL
  module CL = HDSyntax {C = C ^op} (HC ∘F from^op^op) 

  open ORelFunctor ORel

  Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) (SETᴰ ℓS ℓV ) 
  Oᴰ .F-obᴰ (P , Q) o = ⟨ Rel P Q o ⟩ , isProp→isSet (Rel P Q o .snd)
  Oᴰ .F-homᴰ {(v , c)}{(v' , c')}{(f , g)}{(P , Q)}{(P' , Q')}(v'P'≤f*P' , c'Q'≤g*Q) o = RelMono v'P'≤f*P' c'Q'≤g*Q
  Oᴰ .F-idᴰ {(v , c)}{(P , Q)} = 
    -- agda being garbage at figuring out implicits
    ≡out
      (SETᴰ ℓS ℓV)
      {a = O .F-ob (v , c)}
      {b = O .F-ob (v , c)}
      {f = λ z → O .F-hom (id V , id C) z}
      {g = λ z → z}
      {λ o → ⟨ Rel P Q o ⟩ , isProp→isSet (Rel P Q o .snd)}
      {λ o → ⟨ Rel P Q o ⟩ , isProp→isSet (Rel P Q o .snd)}
      {fᴰ =  (λ o → RelMono (idᴰ ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ){x = v , c}{p = P , Q} .fst) (idᴰ ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ){x = v , c}{p = P , Q} .snd))}
      {(λ x z → z)} 
      (ΣPathP (O .F-id , toPathP (funExt λ o → funExt λ r → Rel P Q o .snd _ r)))
  
  Oᴰ .F-seqᴰ {(v , c)}{(v' , c')}{(v'' , c'')}{(f , g)}{(f' , g')}{(P , Q)}{(P' , Q')}{(P'' , Q'')} fᴰ gᴰ =  
    -- agda being garbage at figuring out implicits
    ≡out 
      (SETᴰ ℓS ℓV)
      {a = O .F-ob (v , c)}
      {b = O .F-ob (v'' , c'')}
      {f = O .F-hom (f' ⋆⟨ V ⟩ f , g ⋆⟨ C ⟩ g')}
      {g = λ z → O .F-hom (f' , g') (O .F-hom (f , g) z)}
      {λ o → ⟨ Rel P Q o ⟩ , isProp→isSet (Rel P Q o .snd)}
      {λ o → ⟨ Rel P'' Q'' o ⟩ , isProp→isSet (Rel P'' Q'' o .snd)}
      {fᴰ = (λ o → RelMono ((((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) ⋆ᴰ fᴰ) gᴰ .fst) ((((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) ⋆ᴰ fᴰ) gᴰ .snd))} 
      (ΣPathP (O .F-seq _ _ , toPathP (funExt λ o → funExt λ r → Rel P'' Q'' (O .F-hom (f' , g') (O .F-hom (f , g) o)) .snd _ _ )))
