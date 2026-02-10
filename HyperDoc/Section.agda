module HyperDoc.Section where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 

open import HyperDoc.CBPVModel
open import HyperDoc.CBPVLogic

module _ 
    {ℓVS ℓV'S ℓCS ℓC'S ℓSS ℓVT ℓV'T ℓCT ℓC'T ℓST ℓP ℓP' : Level}
    {M : Model ℓVS ℓV'S ℓCS ℓC'S ℓSS}
    {N : Model ℓVT ℓV'T ℓCT ℓC'T ℓST}
    (F : ModelMorphism _ _ _ _ _ _ _ _ _ _ M N) 
    (LN : Logic {ℓP = ℓP}{ℓP'} N)where

    module M = Model M 
    module N = Model N

    record Section : Type {!   !} where 
      field 
        Vob : {!   !}


  --   (Nᴰ : DisplayedModel _ _ ℓVD ℓVD' _ _  ℓCD ℓCD' _ ℓSD N) where
{- 


module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (F : Functor D C)
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         where
  private
    module C = Category C
    module D = Category D
    module Cᴰ = Categoryᴰ Cᴰ
    module F = Functor F

  -- Section without a qualifier means *local* section.
  record Section : Type (ℓ-max (ℓ-max ℓC ℓC')
                        (ℓ-max (ℓ-max ℓD ℓD')
                        (ℓ-max ℓCᴰ ℓCᴰ')))
    where
    field
      F-obᴰ  : ∀ d → Cᴰ.ob[ F ⟅ d ⟆ ]
      F-homᴰ : ∀ {d d'} (f : D.Hom[ d , d' ])
        → Cᴰ.Hom[ F ⟪ f ⟫ ][ F-obᴰ d , F-obᴰ d' ]
      F-idᴰ : ∀ {d} → F-homᴰ (D.id {d}) Cᴰ.≡[ F .F-id ] Cᴰ.idᴰ
      F-seqᴰ : ∀ {d d' d''}
            → (f : D.Hom[ d , d' ])(g : D.Hom[ d' , d'' ])
            → F-homᴰ (f D.⋆ g) Cᴰ.≡[ F .F-seq f g ] F-homᴰ f Cᴰ.⋆ᴰ F-homᴰ g
-}