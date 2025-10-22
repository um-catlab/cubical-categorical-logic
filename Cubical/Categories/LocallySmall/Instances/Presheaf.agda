module Cubical.Categories.LocallySmall.Instances.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Set
open import Cubical.Categories.LocallySmall.Instances.Functor
open import Cubical.Categories.LocallySmall.Functor

open import Cubical.Categories.LocallySmall.Displayed
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total

open Category
open Categoryᴰ
open Σω
open Liftω

module _ ((Cob , C) : SmallCategory ℓC ℓC') where
  private
    module SET = CategoryᴰNotation SET

  -- TODO put this in a LocallySmall.Presheaf
  -- The current file should be for
  -- the (locally small) category of presheaves
  -- The definitions of presheaves/notation should
  -- be in its own module
  Presheaf : Level → Typeω
  Presheaf ℓP = Functor (C ^op) SET.v[ liftω ℓP ]

  PRESHEAF : Category _ _
  PRESHEAF = ∫C (FIBER-FUNCTOR (Cob , C ^op) SET)

open Functor
module _
  (C : SmallCategory ℓC ℓC')
  (c : ⟨ C ⟩small-ob)
  where
  private
    module C = CategoryNotation (C .snd)
    module SET = CategoryᴰNotation SET

  よ : Presheaf C ℓC'
  よ .F-ob c' = liftω (C.Hom[ c' , liftω c ] , C.isSetHom)
  よ .F-hom f g = f C.⋆ g
  よ .F-id = funExt λ g → C.⋆IdL _
  よ .F-seq {x = x} {y} {z} f g =
    (funExt λ h → C.⋆Assoc g f h)
    ∙ (SET.≡out
         {xᴰ = liftω (C.Hom[ x , liftω c ] , C.isSetHom)}
         {yᴰ = liftω (C.Hom[ z , liftω c ] , C.isSetHom)}
         $
         SET.reind-filler
           {xᴰ = liftω (C.Hom[ x , liftω c ] , C.isSetHom)}
           {yᴰ = liftω (C.Hom[ z , liftω c ] , C.isSetHom)}
           refl λ h → g C.⋆ (f C.⋆ h))

  -- TODO I don't know if we actually want this notation
  -- for an object of the locally small category of
  -- presheaves
  -- _[-,_] : ⟨ PRESHEAF C ⟩ob
  -- _[-,_] .fst = liftω ℓC'
  -- _[-,_] .snd = よ

-- TODO put this in a LocallySmall.Presheaf
module PresheafNotation {ℓC}{ℓC'}
  {C : SmallCategory ℓC ℓC'}
  {ℓP}
  (P : Presheaf C ℓP)
  where
  p[_] : ⟨ C ⟩small-ob → Type ℓP
  p[ c ] = ⟨ P .F-ob (liftω c) .lowerω ⟩
