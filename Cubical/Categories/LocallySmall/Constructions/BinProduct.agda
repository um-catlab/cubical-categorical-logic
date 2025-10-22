module Cubical.Categories.LocallySmall.Constructions.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Variables

open Category
open Σω

module _
  (C : Category Cob CHom-ℓ)
  (D : Category Dob DHom-ℓ)
  where
  private
    module C = Category C
    module D = Category D

  _×C_ : Category (Σω[ c ∈ Cob ] Dob) _
  _×C_ .Hom[_,_] (c , d) (c' , d') =
    C.Hom[ c , c' ] × D.Hom[ d , d' ]
  _×C_ .id = C.id , D.id
  _×C_ ._⋆_ = λ f g → f .fst C.⋆ g .fst , f .snd D.⋆ g .snd
  _×C_ .⋆IdL f = ≡-× (C.⋆IdL (f .fst)) (D.⋆IdL (f .snd))
  _×C_ .⋆IdR f = ≡-× (C.⋆IdR (f .fst)) (D.⋆IdR (f .snd))
  _×C_ .⋆Assoc f g h =
    ≡-×
      (C.⋆Assoc (f .fst) (g .fst) (h .fst))
      (D.⋆Assoc (f .snd) (g .snd) (h .snd))
  _×C_ .isSetHom = isSet× C.isSetHom D.isSetHom
