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
    (F : ModelMorphism _ _ _ _ _ _ _ _ _ _ M N) 
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

      SectionO : Type _ 
      SectionO = 
        ∀ 
          {A : ob M.V}
          {B : ob M.C}
          (M : M.O .F-ob (A , B) .fst) → 
        Oᴰ .F-obᴰ {FV .F-ob A , FC .F-ob B} (SV.F-obᴰ A , SC.F-obᴰ B) (FO .N-ob (A , B) M) .fst

    MSection : Type _ 
    MSection = Σ[ SV ∈ Section FV Vᴰ ] Σ[ SC ∈ Section FC Cᴰ ] SectionO SV SC

{-}
    module _ where 
      Sect : MSection
      Sect = GlobalSectionReindex→Section Vᴰ FV {!   !} , GlobalSectionReindex→Section Cᴰ FC {!   !} , {!   !}
-}

      {-
        module _
    {D : Category ℓD ℓD'}
    {F : Functor |FreeCartesianCategory| D}
    (Dᴰ : CartesianCategoryⱽ D ℓDᴰ ℓDᴰ') where
    private
      module Dᴰ = CartesianCategoryⱽ Dᴰ
    F*Dᴰ-cartⱽ = CartReindex.reindex F Dᴰ
    F*Dᴰ : CartesianCategoryᴰ FreeCartesianCategory _ _
    F*Dᴰ = CartesianCategoryⱽ→CartesianCategoryᴰ F*Dᴰ-cartⱽ
    open CartesianCategoryᴰ


    elimLocal : ∀ (ı : Interpᴰ F*Dᴰ) → Section F Dᴰ.Cᴰ
    elimLocal ı = GlobalSectionReindex→Section _ _ (elim F*Dᴰ ı)

      -}
      -- Section FV Vᴰ × Section FC Cᴰ × SectionO
        

{-
    -- unfolding of Section on a converted hyperdoc
    -- dropping id and seq
    record Section : Type (levels (ℓVS ∷ ℓV'S ∷ ℓCS ∷ ℓC'S ∷ ℓSS ∷ ℓVT ∷ ℓV'T ∷ ℓCT ∷ ℓC'T ∷ ℓST ∷ ℓP ∷ ℓP' ∷ [])) where 
      field 
        DobV : (v : M.V .ob) → VH'.F∣ v ∣ 
        DhomV : {v v' : M.V .ob }(f : M.V [ v , v' ]) → 
          v VH'.◂ DobV v ≤ VH'.f* f (DobV v')

        DobC : (c : M.C .ob) → CH'.F∣ c ∣ 
        DhomC : {c c' : M.C .ob }(f : M.C [ c , c' ]) → 
          c CH'.◂ DobC c ≤ CH'.f* f (DobC c')

        -- hrm.. 

module _ 
  {ℓV ℓV' ℓC ℓC' ℓS ℓP ℓP' : Level}
  {M : Model ℓV ℓV' ℓC ℓC' ℓS}
  (L : Logic {ℓP = ℓP}{ℓP'} M)
  where

  GlobalSection : Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ ℓP ∷ ℓP' ∷ []))
  GlobalSection = Section {M = M}{M} (idModelMorphism M) L
  -}