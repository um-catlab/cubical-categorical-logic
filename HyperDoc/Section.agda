module HyperDoc.Section where

open import Cubical.Data.List using (_∷_ ; [])
open import Cubical.Data.Sigma

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Posets
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Displayed.Constructions.Reindex.Base

open import HyperDoc.CBPVModel
open import HyperDoc.CBPVLogic
open import HyperDoc.Syntax
open import HyperDoc.Lib
open import HyperDoc.AsDisplayed

open Category
open Functor 
open Functorᴰ
open Categoryᴰ
open PshHom


module _ 
    {ℓVS ℓV'S ℓCS ℓC'S  ℓVT ℓV'T ℓCT ℓC'T  ℓP ℓP' : Level}
    {M : Model ℓVS ℓV'S ℓCS ℓC'S (ℓ-max ℓP ℓP')}
    {N : Model ℓVT ℓV'T ℓCT ℓC'T (ℓ-max ℓP ℓP')}
    (F : ModelMorphism ℓVS ℓV'S ℓCS ℓC'S (ℓ-max ℓP ℓP') ℓVT ℓV'T ℓCT ℓC'T (ℓ-max ℓP ℓP') M N) 
    (LN : Logic {ℓP = ℓP}{ℓP'} N)where

    open ModelMorphism F
    private 
      module M = Model M 
      module N = Model N
      module L = Logic LN
      module VH' = HDSyntax (L.VH ∘F (FV ^opF))
      module CH' = HDSyntax (L.CH ∘F (FC ^opF))

    open Modelᴰ N LN
  
    module _ 
      (SV : Section FV Vᴰ) 
      (SC : Section FC Cᴰ) where 

      private 
        module SV = Section SV 
        module SC = Section SC

      SectionO : Type (ℓ-max (ℓ-max (ℓ-max ℓVS ℓCS) ℓP) ℓP')
      SectionO = 
        ∀ 
          {A : ob M.V}
          {B : ob M.C}
          (M : M.O .F-ob (A , B) .fst) → 
        Oᴰ .F-obᴰ {FV .F-ob A , FC .F-ob B} (SV.F-obᴰ A , SC.F-obᴰ B) (FO .N-ob (A , B) M) .fst

    MSection : Type _
    MSection = Σ[ SV ∈ Section FV Vᴰ ] Σ[ SC ∈ Section FC Cᴰ ] SectionO SV SC

MGlobalSection : {ℓV ℓV' ℓC ℓC'  ℓP ℓP' : Level}{M : Model ℓV ℓV' ℓC ℓC' (ℓ-max ℓP ℓP') }(L : Logic {ℓP = ℓP}{ℓP'} M) → Type _ 
MGlobalSection {M = M} L = MSection (idModelMorphism M) L

module KungFoo where 


{-}
    module _ where 
      Sect : MSection
      Sect = GlobalSectionReindex→Section Vᴰ FV {!   !} , GlobalSectionReindex→Section Cᴰ FC {!   !} , {!   !}
-}
