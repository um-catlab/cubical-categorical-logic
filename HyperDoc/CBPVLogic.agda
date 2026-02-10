module HyperDoc.CBPVLogic where 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Category 
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor

open import Cubical.Data.List using (_∷_ ; [])

open import HyperDoc.CBPVModel 
open import HyperDoc.Syntax
open import HyperDoc.Lib

open Functor

record Logic 
  {ℓV ℓV' ℓC ℓC' ℓS ℓP ℓP'  : Level}
  (M : Model ℓV ℓV' ℓC ℓC' ℓS) : Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ ℓ-suc ℓP ∷ ℓ-suc ℓP' ∷ [])) where 
  open Model M
  field 
    VH : Functor (V ^op) (POSET ℓP ℓP')
    CH : Functor (C ^op) (POSET ℓP ℓP')
    pushV : ∀{A}{B} → (f : O[ A , B ]) →  MonFun (VH .F-ob A .fst) (CH .F-ob B .fst)
    pullC : ∀{A}{B} → (f : O[ A , B ]) →  MonFun (CH .F-ob B .fst) (VH .F-ob A .fst)
    pushPullAdj :  ∀{A}{B}{o} → pushV {A}{B} o ⊣ pullC o  
    -- + coherence condition for pull with VH and CH


{-
module _ 
  {ℓV ℓV' ℓC ℓC' ℓS ℓP ℓP' ℓR : Level}
  {M : Model ℓV ℓV' ℓC ℓC' ℓS }
  (L : Logic {ℓP = ℓP}{ℓP'} M) where 

  open Model M
  open Logic L

  module VL = HDSyntax VH 
  module CL = HDSyntax CH 

  HasUF⊣ : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓV ℓC) ℓS) ℓP) ℓP')
  HasUF⊣ = ∀{A}{B} → (f : O[ A , B ]) → 
    Σ[ f→  ∈ MonFun (VH .F-ob A .fst) (CH .F-ob B .fst) ] 
    Σ[ f←  ∈ MonFun (CH .F-ob B .fst) (VH .F-ob A .fst) ] 
    (f→ ⊣ f←)
-}

{-
module _ 
  {ℓV ℓV' ℓC ℓC' ℓS ℓP ℓP' ℓR : Level}
  (M : Model ℓV ℓV' ℓC ℓC' ℓS)
  where
  
  open Model M


  -- this is the data of a displayed profunctor in our setting (proof irrelevant)
  record ORelFunctor 
    (HL : Functor (V ^op) (POSET ℓP ℓP'))
    (HC : Functor C (POSET ℓP ℓP'))
    : Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ ℓP ∷ ℓP' ∷ ℓ-suc ℓR ∷ []))  where
    private 
      module LV = HDSyntax HL
      module LC = HDSyntax {C = C ^op} (HC ∘F from^op^op)
    field 
      Rel : ∀{v c} → LV.F∣ v ∣ → LC.F∣ c ∣ → O[ v , c ] → hProp ℓR
      RelMono :  
        ∀ {v v' c c' o}{P : LV.F∣ v ∣}{ P' : LV.F∣ v' ∣}{Q : LC.F∣ c ∣}{Q' : LC.F∣ c' ∣} → 
        {f : V [ v' , v ]} → 
        {g : C [ c , c' ]} → 
        (P≤ : v' LV.◂ P' ≤ LV.f* f P ) -- pull back
        --(Q≤ : c' LC.◂ LC.f* g Q ≤ Q' ) -- push forward, easy instantiate but wrong
        (Q≤ : c' LC.◂ Q' ≤ LC.f* g Q ) -- works for displayed profunctor proof
        (R : ⟨ Rel P Q o ⟩ ) → 
        ⟨ Rel P' Q' (O .F-hom (f , g ) o) ⟩ 
      
    Rel[_][_,_] : ∀{v c} → ⟨ O ⟅ (v , c) ⟆ ⟩ → LV.F∣ v ∣ → LC.F∣ c ∣ → hProp ℓR
    Rel[_][_,_] o P Q = Rel P Q o

-}