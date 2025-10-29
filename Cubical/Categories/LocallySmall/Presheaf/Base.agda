module Cubical.Categories.LocallySmall.Presheaf.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Set
open import Cubical.Categories.LocallySmall.Instances.Functor
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.NaturalTransformation.Base

open import Cubical.Categories.LocallySmall.Displayed
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total

open Category
open Categoryᴰ
open Σω
open Liftω

module _ ((Cob , C) : SmallCategory ℓC ℓC') where
  private
    module SET = CategoryᴰNotation SET

  Presheaf : Level → Typeω
  Presheaf ℓP = Functor (C ^op) SET.v[ liftω ℓP ]

  PRESHEAF : Categoryᴰ LEVEL (λ d → Functor (C ^op) SET.v[ d ]) _
  PRESHEAF = FIBER-FUNCTOR (Cob , C ^op) SET

module _ {C : SmallCategory ℓC ℓC'} where
  mkPshOb : ∀ {ℓP} → Presheaf C ℓP → ⟨ ∫C (PRESHEAF C) ⟩ob
  mkPshOb P .fst = liftω _
  mkPshOb P .snd = P

open Functor
module _
  (C : SmallCategory ℓC ℓC')
  (c : ⟨ C ⟩small-ob)
  where
  private
    module C = CategoryNotation (C .snd)
    module SET = CategoryᴰNotation SET

  _[-,_] : Presheaf C ℓC'
  _[-,_] .F-ob c' = liftω (C.Hom[ c' , liftω c ] , C.isSetHom)
  _[-,_] .F-hom f g = f C.⋆ g
  _[-,_] .F-id = funExt λ g → C.⋆IdL _
  _[-,_] .F-seq {x = x} {y} {z} f g =
    (funExt λ h → C.⋆Assoc g f h)
    ∙ (SET.≡out
         {xᴰ = liftω (C.Hom[ x , liftω c ] , C.isSetHom)}
         {yᴰ = liftω (C.Hom[ z , liftω c ] , C.isSetHom)}
         $
         SET.reind-filler
           {xᴰ = liftω (C.Hom[ x , liftω c ] , C.isSetHom)}
           {yᴰ = liftω (C.Hom[ z , liftω c ] , C.isSetHom)}
           refl λ h → g C.⋆ (f C.⋆ h))

open SmallFibNatTrans
module _
  (C : SmallCategory ℓC ℓC')
  (c : ⟨ C ⟩small-ob)
  where
  private
    module C = CategoryNotation (C .snd)
    module SET = CategoryᴰNotation SET
    module PSH = CategoryᴰNotation (PRESHEAF C)
    module ∫PSH = CategoryNotation (∫C (PRESHEAF C))
  よ : Functor ⟨ C ⟩smallcat (∫C (PRESHEAF C))
  よ .F-ob (liftω c) = mkPshOb (C [-, c ])
  よ .F-hom f .fst = _
  よ .F-hom f .snd .N-ob c g = g C.⋆ f
  よ .F-hom {x = x}{y = y} f .snd .N-hom g =
    N-hom'→N-hom SET _ (C [-, x .lowerω ]) (C [-, y .lowerω ])
      (よ .F-hom f .snd .N-ob) g
      (ΣPathP (refl , funExt λ _ → C.⋆Assoc _ _ _))
  よ .F-id =
    makeSFNatTransPath refl
      (λ _ → ΣPathP (refl , funExt λ _ → C.⋆IdR _))
  よ .F-seq f g =
    makeSFNatTransPath refl
      (λ _ → ΣPathP (refl , funExt λ _ → sym $ C.⋆Assoc _ _ _ ))

-- TODO port presheaf notation
module PresheafNotation {ℓC}{ℓC'}
  {C : SmallCategory ℓC ℓC'}
  {ℓP}
  (P : Presheaf C ℓP)
  where
  p[_] : ⟨ C ⟩small-ob → Type ℓP
  p[ c ] = ⟨ P .F-ob (liftω c) .lowerω ⟩
