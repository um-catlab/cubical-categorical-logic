module HyperDoc.Section where

open import Cubical.Data.List using (_∷_ ; [])

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Posets

open import HyperDoc.CBPVModel
open import HyperDoc.CBPVLogic
open import HyperDoc.Syntax
open import HyperDoc.Lib

open Category
open Functor 

{-}
module _ 
    {ℓVS ℓV'S ℓCS ℓC'S ℓSS ℓVT ℓV'T ℓCT ℓC'T ℓST ℓP ℓP' : Level}
    {M : Model ℓVS ℓV'S ℓCS ℓC'S ℓSS}
    {N : Model ℓVT ℓV'T ℓCT ℓC'T ℓST}
    (F : ModelMorphism _ _ _ _ _ _ _ _ _ _ M N) 
    (LN : Logic {ℓP = ℓP}{ℓP'} N)where

    open ModelMorphism F
    private 
      module M = Model M 
      module N = Model N
      module L = Logic LN
      module VH' = HDSyntax (L.VH ∘F (FV ^opF))
      module CH' = HDSyntax (L.CH ∘F (FC ^opF))


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